/*-
 * Copyright 2013, winocm <winocm@icloud.com>
 * Copyright 2013, planetbeing.
 * All rights reserved.
 *
 * This program is free software; you can redistribute it and/or
 * modify it under the terms of the GNU General Public License
 * as published by the Free Software Foundation; either version 2
 * of the License, or (at your option) any later version.
 *
 * This program is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 *
 * You should have received a copy of the GNU General Public License
 * along with this program; if not, write to the Free Software
 * Foundation, Inc., 51 Franklin Street, Fifth Floor, Boston, MA  02110-1301, USA.
 *
 * $Id$
 */

#include <sys/cdefs.h>
#include <sys/types.h>
#include <sys/errno.h>
#include <sys/stat.h>
#include <string.h>
#include <stdlib.h>
#include <stdint.h>
#include <stdio.h>
#include <ctype.h>
#include <err.h>

#include <assert.h>
#include "structs.h"
#include "patch.h"
#include "util.h"
#include "macho_loader.h"
#include "kcache.h"

#define KERNEL_VMADDR		0x80001000

static struct kernel_interval intervals[] = {
	{1357, 1358, 3.0f},
	{1504, 1505, 4.0f},
	{1735, 1736, 4.3f},
	{1878, 1879, 5.0f},
	{2107, 2108, 6.0f},
	{2423, 2424, 7.0f},
};

static struct mapped_image current_image;

struct compressed_kernel_header
{
	u_int32_t signature;
	u_int32_t compress_type;
	u_int32_t adler32;
	u_int32_t uncompressed_size;
	u_int32_t compressed_size;
	u_int32_t reserved[11];
	char platform_name[64];
	char root_path[256];
	u_int8_t data[0];
};

static uint32_t
bit_range (uint32_t x, int start, int end)
{
	x = (x << (31 - start)) >> (31 - start);
	x = (x >> end);
	return x;
}

static uint32_t
ror (uint32_t x, int places)
{
	return (x >> places) | (x << (32 - places));
}

static int
thumb_expand_imm_c (uint16_t imm12)
{
	if (bit_range (imm12, 11, 10) == 0) {
		switch (bit_range (imm12, 9, 8)) {
		case 0:
			return bit_range (imm12, 7, 0);
		case 1:
			return (bit_range (imm12, 7, 0) << 16) | bit_range (imm12, 7, 0);
		case 2:
			return (bit_range (imm12, 7, 0) << 24) | (bit_range (imm12, 7, 0) << 8);
		case 3:
			return (bit_range (imm12, 7, 0) << 24) | (bit_range (imm12, 7, 0) << 16) | (bit_range (imm12, 7, 0) << 8) | bit_range (imm12, 7, 0);
		default:
			return 0;
		}
	}
	else {
		uint32_t unrotated_value = 0x80 | bit_range (imm12, 6, 0);
		return ror (unrotated_value, bit_range (imm12, 11, 7));
	}
}

static int
insn_is_32bit (uint16_t * i)
{
	return (*i & 0xe000) == 0xe000 && (*i & 0x1800) != 0x0;
}

static int
insn_is_bl (uint16_t * i)
{
	if ((*i & 0xf800) == 0xf000 && (*(i + 1) & 0xd000) == 0xd000)
		return 1;
	else if ((*i & 0xf800) == 0xf000 && (*(i + 1) & 0xd001) == 0xc000)
		return 1;
	else
		return 0;
}

static uint32_t
insn_bl_imm32 (uint16_t * i)
{
	uint16_t insn0 = *i;
	uint16_t insn1 = *(i + 1);
	uint32_t s = (insn0 >> 10) & 1;
	uint32_t j1 = (insn1 >> 13) & 1;
	uint32_t j2 = (insn1 >> 11) & 1;
	uint32_t i1 = ~(j1 ^ s) & 1;
	uint32_t i2 = ~(j2 ^ s) & 1;
	uint32_t imm10 = insn0 & 0x3ff;
	uint32_t imm11 = insn1 & 0x7ff;
	uint32_t imm32 = (imm11 << 1) | (imm10 << 12) | (i2 << 22) | (i1 << 23) | (s ? 0xff000000 : 0);
	return imm32;
}

static int
insn_is_b_conditional (uint16_t * i)
{
	return (*i & 0xF000) == 0xD000 && (*i & 0x0F00) != 0x0F00 && (*i & 0x0F00) != 0xE;
}

static int
insn_is_b_unconditional (uint16_t * i)
{
	if ((*i & 0xF800) == 0xE000)
		return 1;
	else if ((*i & 0xF800) == 0xF000 && (*(i + 1) & 0xD000) == 9)
		return 1;
	else
		return 0;
}

static int
insn_is_ldr_literal (uint16_t * i)
{
	return (*i & 0xF800) == 0x4800 || (*i & 0xFF7F) == 0xF85F;
}

static int
insn_ldr_literal_rt (uint16_t * i)
{
	if ((*i & 0xF800) == 0x4800)
		return (*i >> 8) & 7;
	else if ((*i & 0xFF7F) == 0xF85F)
		return (*(i + 1) >> 12) & 0xF;
	else
		return 0;
}

static int
insn_ldr_literal_imm (uint16_t * i)
{
	if ((*i & 0xF800) == 0x4800)
		return (*i & 0xF) << 2;
	else if ((*i & 0xFF7F) == 0xF85F)
		return (*(i + 1) & 0xFFF) * (((*i & 0x0800) == 0x0800) ? 1 : -1);
	else
		return 0;
}

// TODO: More encodings
static int
insn_is_ldr_imm (uint16_t * i)
{
	uint8_t opA = bit_range (*i, 15, 12);
	uint8_t opB = bit_range (*i, 11, 9);

	return opA == 6 && (opB & 4) == 4;
}

static int
insn_ldr_imm_rt (uint16_t * i)
{
	return (*i & 7);
}

static int
insn_ldr_imm_rn (uint16_t * i)
{
	return ((*i >> 3) & 7);
}

static int
insn_ldr_imm_imm (uint16_t * i)
{
	return ((*i >> 6) & 0x1F);
}

// TODO: More encodings
static int
insn_is_ldrb_imm (uint16_t * i)
{
	return (*i & 0xF800) == 0x7800;
}

static int
insn_ldrb_imm_rt (uint16_t * i)
{
	return (*i & 7);
}

static int
insn_ldrb_imm_rn (uint16_t * i)
{
	return ((*i >> 3) & 7);
}

static int
insn_ldrb_imm_imm (uint16_t * i)
{
	return ((*i >> 6) & 0x1F);
}

static int
insn_is_ldr_reg (uint16_t * i)
{
	if ((*i & 0xFE00) == 0x5800)
		return 1;
	else if ((*i & 0xFFF0) == 0xF850 && (*(i + 1) & 0x0FC0) == 0x0000)
		return 1;
	else
		return 0;
}

static int
insn_ldr_reg_rn (uint16_t * i)
{
	if ((*i & 0xFE00) == 0x5800)
		return (*i >> 3) & 0x7;
	else if ((*i & 0xFFF0) == 0xF850 && (*(i + 1) & 0x0FC0) == 0x0000)
		return (*i & 0xF);
	else
		return 0;
}

int
insn_ldr_reg_rt (uint16_t * i)
{
	if ((*i & 0xFE00) == 0x5800)
		return *i & 0x7;
	else if ((*i & 0xFFF0) == 0xF850 && (*(i + 1) & 0x0FC0) == 0x0000)
		return (*(i + 1) >> 12) & 0xF;
	else
		return 0;
}

int
insn_ldr_reg_rm (uint16_t * i)
{
	if ((*i & 0xFE00) == 0x5800)
		return (*i >> 6) & 0x7;
	else if ((*i & 0xFFF0) == 0xF850 && (*(i + 1) & 0x0FC0) == 0x0000)
		return *(i + 1) & 0xF;
	else
		return 0;
}

static int
insn_ldr_reg_lsl (uint16_t * i)
{
	if ((*i & 0xFE00) == 0x5800)
		return 0;
	else if ((*i & 0xFFF0) == 0xF850 && (*(i + 1) & 0x0FC0) == 0x0000)
		return (*(i + 1) >> 4) & 0x3;
	else
		return 0;
}

static int
insn_is_add_reg (uint16_t * i)
{
	if ((*i & 0xFE00) == 0x1800)
		return 1;
	else if ((*i & 0xFF00) == 0x4400)
		return 1;
	else if ((*i & 0xFFE0) == 0xEB00)
		return 1;
	else
		return 0;
}

static int
insn_add_reg_rd (uint16_t * i)
{
	if ((*i & 0xFE00) == 0x1800)
		return (*i & 7);
	else if ((*i & 0xFF00) == 0x4400)
		return (*i & 7) | ((*i & 0x80) >> 4);
	else if ((*i & 0xFFE0) == 0xEB00)
		return (*(i + 1) >> 8) & 0xF;
	else
		return 0;
}

static int
insn_add_reg_rn (uint16_t * i)
{
	if ((*i & 0xFE00) == 0x1800)
		return ((*i >> 3) & 7);
	else if ((*i & 0xFF00) == 0x4400)
		return (*i & 7) | ((*i & 0x80) >> 4);
	else if ((*i & 0xFFE0) == 0xEB00)
		return (*i & 0xF);
	else
		return 0;
}

static int
insn_add_reg_rm (uint16_t * i)
{
	if ((*i & 0xFE00) == 0x1800)
		return (*i >> 6) & 7;
	else if ((*i & 0xFF00) == 0x4400)
		return (*i >> 3) & 0xF;
	else if ((*i & 0xFFE0) == 0xEB00)
		return *(i + 1) & 0xF;
	else
		return 0;
}

static int
insn_is_movt (uint16_t * i)
{
	return (*i & 0xFBF0) == 0xF2C0 && (*(i + 1) & 0x8000) == 0;
}

static int
insn_movt_rd (uint16_t * i)
{
	return (*(i + 1) >> 8) & 0xF;
}

static int
insn_movt_imm (uint16_t * i)
{
	return ((*i & 0xF) << 12) | ((*i & 0x0400) << 1) | ((*(i + 1) & 0x7000) >> 4) | (*(i + 1) & 0xFF);
}

static int
insn_is_mov_imm (uint16_t * i)
{
	if ((*i & 0xF800) == 0x2000)
		return 1;
	else if ((*i & 0xFBEF) == 0xF04F && (*(i + 1) & 0x8000) == 0)
		return 1;
	else if ((*i & 0xFBF0) == 0xF240 && (*(i + 1) & 0x8000) == 0)
		return 1;
	else
		return 0;
}

static int
insn_mov_imm_rd (uint16_t * i)
{
	if ((*i & 0xF800) == 0x2000)
		return (*i >> 8) & 7;
	else if ((*i & 0xFBEF) == 0xF04F && (*(i + 1) & 0x8000) == 0)
		return (*(i + 1) >> 8) & 0xF;
	else if ((*i & 0xFBF0) == 0xF240 && (*(i + 1) & 0x8000) == 0)
		return (*(i + 1) >> 8) & 0xF;
	else
		return 0;
}

static int
insn_mov_imm_imm (uint16_t * i)
{
	if ((*i & 0xF800) == 0x2000)
		return *i & 0xF;
	else if ((*i & 0xFBEF) == 0xF04F && (*(i + 1) & 0x8000) == 0)
		return thumb_expand_imm_c (((*i & 0x0400) << 1) | ((*(i + 1) & 0x7000) >> 4) | (*(i + 1) & 0xFF));
	else if ((*i & 0xFBF0) == 0xF240 && (*(i + 1) & 0x8000) == 0)
		return ((*i & 0xF) << 12) | ((*i & 0x0400) << 1) | ((*(i + 1) & 0x7000) >> 4) | (*(i + 1) & 0xFF);
	else
		return 0;
}

static int
insn_is_cmp_imm (uint16_t * i)
{
	if ((*i & 0xF800) == 0x2800)
		return 1;
	else if ((*i & 0xFBF0) == 0xF1B0 && (*(i + 1) & 0x8F00) == 0x0F00)
		return 1;
	else
		return 0;
}

static int
insn_cmp_imm_rn (uint16_t * i)
{
	if ((*i & 0xF800) == 0x2800)
		return (*i >> 8) & 7;
	else if ((*i & 0xFBF0) == 0xF1B0 && (*(i + 1) & 0x8F00) == 0x0F00)
		return *i & 0xF;
	else
		return 0;
}

static int
insn_cmp_imm_imm (uint16_t * i)
{
	if ((*i & 0xF800) == 0x2800)
		return *i & 0xFF;
	else if ((*i & 0xFBF0) == 0xF1B0 && (*(i + 1) & 0x8F00) == 0x0F00)
		return thumb_expand_imm_c (((*i & 0x0400) << 1) | ((*(i + 1) & 0x7000) >> 4) | (*(i + 1) & 0xFF));
	else
		return 0;
}

static int
insn_is_and_imm (uint16_t * i)
{
	return (*i & 0xFBE0) == 0xF000 && (*(i + 1) & 0x8000) == 0;
}

static int
insn_and_imm_rn (uint16_t * i)
{
	return *i & 0xF;
}

static int
insn_and_imm_rd (uint16_t * i)
{
	return (*(i + 1) >> 8) & 0xF;
}

static int
insn_and_imm_imm (uint16_t * i)
{
	return thumb_expand_imm_c (((*i & 0x0400) << 1) | ((*(i + 1) & 0x7000) >> 4) | (*(i + 1) & 0xFF));
}

static int
insn_is_push (uint16_t * i)
{
	if ((*i & 0xFE00) == 0xB400)
		return 1;
	else if (*i == 0xE92D)
		return 1;
	else if (*i == 0xF84D && (*(i + 1) & 0x0FFF) == 0x0D04)
		return 1;
	else
		return 0;
}

static int
insn_push_registers (uint16_t * i)
{
	if ((*i & 0xFE00) == 0xB400)
		return (*i & 0x00FF) | ((*i & 0x0100) << 6);
	else if (*i == 0xE92D)
		return *(i + 1);
	else if (*i == 0xF84D && (*(i + 1) & 0x0FFF) == 0x0D04)
		return 1 << ((*(i + 1) >> 12) & 0xF);
	else
		return 0;
}

static int
insn_is_preamble_push (uint16_t * i)
{
	return insn_is_push (i) && (insn_push_registers (i) & (1 << 14)) != 0;
}

static int
insn_is_str_imm (uint16_t * i)
{
	if ((*i & 0xF800) == 0x6000)
		return 1;
	else if ((*i & 0xF800) == 0x9000)
		return 1;
	else if ((*i & 0xFFF0) == 0xF8C0)
		return 1;
	else if ((*i & 0xFFF0) == 0xF840 && (*(i + 1) & 0x0800) == 0x0800)
		return 1;
	else
		return 0;
}

static int
insn_str_imm_postindexed (uint16_t * i)
{
	if ((*i & 0xF800) == 0x6000)
		return 1;
	else if ((*i & 0xF800) == 0x9000)
		return 1;
	else if ((*i & 0xFFF0) == 0xF8C0)
		return 1;
	else if ((*i & 0xFFF0) == 0xF840 && (*(i + 1) & 0x0800) == 0x0800)
		return (*(i + 1) >> 10) & 1;
	else
		return 0;
}

static int
insn_str_imm_wback (uint16_t * i)
{
	if ((*i & 0xF800) == 0x6000)
		return 0;
	else if ((*i & 0xF800) == 0x9000)
		return 0;
	else if ((*i & 0xFFF0) == 0xF8C0)
		return 0;
	else if ((*i & 0xFFF0) == 0xF840 && (*(i + 1) & 0x0800) == 0x0800)
		return (*(i + 1) >> 8) & 1;
	else
		return 0;
}

static int
insn_str_imm_imm (uint16_t * i)
{
	if ((*i & 0xF800) == 0x6000)
		return (*i & 0x07C0) >> 4;
	else if ((*i & 0xF800) == 0x9000)
		return (*i & 0xFF) << 2;
	else if ((*i & 0xFFF0) == 0xF8C0)
		return (*(i + 1) & 0xFFF);
	else if ((*i & 0xFFF0) == 0xF840 && (*(i + 1) & 0x0800) == 0x0800)
		return (*(i + 1) & 0xFF);
	else
		return 0;
}

static int
insn_str_imm_rt (uint16_t * i)
{
	if ((*i & 0xF800) == 0x6000)
		return (*i & 7);
	else if ((*i & 0xF800) == 0x9000)
		return (*i >> 8) & 7;
	else if ((*i & 0xFFF0) == 0xF8C0)
		return (*(i + 1) >> 12) & 0xF;
	else if ((*i & 0xFFF0) == 0xF840 && (*(i + 1) & 0x0800) == 0x0800)
		return (*(i + 1) >> 12) & 0xF;
	else
		return 0;
}

static int
insn_str_imm_rn (uint16_t * i)
{
	if ((*i & 0xF800) == 0x6000)
		return (*i >> 3) & 7;
	else if ((*i & 0xF800) == 0x9000)
		return 13;
	else if ((*i & 0xFFF0) == 0xF8C0)
		return (*i & 0xF);
	else if ((*i & 0xFFF0) == 0xF840 && (*(i + 1) & 0x0800) == 0x0800)
		return (*i & 0xF);
	else
		return 0;
}


// Given an instruction, search backwards until an instruction is found matching the specified criterion.
static uint16_t *
find_last_insn_matching (uint32_t region, uint8_t * kdata, size_t ksize, uint16_t * current_instruction, int (*match_func) (uint16_t *))
{
	while ((uintptr_t) current_instruction > (uintptr_t) kdata) {
		if (insn_is_32bit (current_instruction - 2) && !insn_is_32bit (current_instruction - 3)) {
			current_instruction -= 2;
		}
		else {
			--current_instruction;
		}

		if (match_func (current_instruction)) {
			return current_instruction;
		}
	}

	return NULL;
}

// Given an instruction and a register, find the PC-relative address that was stored inside the register by the time the instruction was reached.
static uint32_t
find_pc_rel_value (uint32_t region, uint8_t * kdata, size_t ksize, uint16_t * insn, int reg)
{
	// Find the last instruction that completely wiped out this register
	int found = 0;
	uint16_t *current_instruction = insn;
	while ((uintptr_t) current_instruction > (uintptr_t) kdata) {
		if (insn_is_32bit (current_instruction - 2)) {
			current_instruction -= 2;
		}
		else {
			--current_instruction;
		}

		if (insn_is_mov_imm (current_instruction) && insn_mov_imm_rd (current_instruction) == reg) {
			found = 1;
			break;
		}

		if (insn_is_ldr_literal (current_instruction) && insn_ldr_literal_rt (current_instruction) == reg) {
			found = 1;
			break;
		}
	}

	if (!found)
		return 0;

	// Step through instructions, executing them as a virtual machine, only caring about instructions that affect the target register and are commonly used for PC-relative addressing.
	uint32_t value = 0;
	while ((uintptr_t) current_instruction < (uintptr_t) insn) {
		if (insn_is_mov_imm (current_instruction) && insn_mov_imm_rd (current_instruction) == reg) {
			value = insn_mov_imm_imm (current_instruction);
		}
		else if (insn_is_ldr_literal (current_instruction) && insn_ldr_literal_rt (current_instruction) == reg) {
			value = *(uint32_t *) (kdata + (((((uintptr_t) current_instruction - (uintptr_t) kdata) + 4) & 0xFFFFFFFC) + insn_ldr_literal_imm (current_instruction)));
		}
		else if (insn_is_movt (current_instruction) && insn_movt_rd (current_instruction) == reg) {
			value |= insn_movt_imm (current_instruction) << 16;
		}
		else if (insn_is_add_reg (current_instruction) && insn_add_reg_rd (current_instruction) == reg) {
			if (insn_add_reg_rm (current_instruction) != 15 || insn_add_reg_rn (current_instruction) != reg) {
				// Can't handle this kind of operation!
				return 0;
			}

			value += ((uintptr_t) current_instruction - (uintptr_t) kdata) + 4;
		}

		current_instruction += insn_is_32bit (current_instruction) ? 2 : 1;
	}

	return value;
}

// Find PC-relative references to a certain address (relative to kdata). This is basically a virtual machine that only cares about instructions used in PC-relative addressing, so no branches, etc.
static uint16_t *
find_literal_ref (uint32_t region, uint8_t * kdata, size_t ksize, uint16_t * insn, uint32_t address)
{
	uint16_t *current_instruction = insn;
	uint32_t value[16];
	memset (value, 0, sizeof (value));

	while ((uintptr_t) current_instruction < (uintptr_t) (kdata + ksize)) {
		if (insn_is_mov_imm (current_instruction)) {
			value[insn_mov_imm_rd (current_instruction)] = insn_mov_imm_imm (current_instruction);
		}
		else if (insn_is_ldr_literal (current_instruction)) {
			uintptr_t literal_address = (uintptr_t) kdata + ((((uintptr_t) current_instruction - (uintptr_t) kdata) + 4) & 0xFFFFFFFC) + insn_ldr_literal_imm (current_instruction);
			if (literal_address >= (uintptr_t) kdata && (literal_address + 4) <= ((uintptr_t) kdata + ksize)) {
				value[insn_ldr_literal_rt (current_instruction)] = *(uint32_t *) (literal_address);
			}
		}
		else if (insn_is_movt (current_instruction)) {
			value[insn_movt_rd (current_instruction)] |= insn_movt_imm (current_instruction) << 16;
		}
		else if (insn_is_add_reg (current_instruction)) {
			int reg = insn_add_reg_rd (current_instruction);
			if (insn_add_reg_rm (current_instruction) == 15 && insn_add_reg_rn (current_instruction) == reg) {
				value[reg] += ((uintptr_t) current_instruction - (uintptr_t) kdata) + 4;
				if (value[reg] == address) {
					return current_instruction;
				}
			}
		}

		current_instruction += insn_is_32bit (current_instruction) ? 2 : 1;
	}

	return NULL;
}

struct find_search_mask
{
	uint16_t mask;
	uint16_t value;
};

// Search the range of kdata for a series of 16-bit values that match the search mask.
static uint16_t *
find_with_search_mask (uint32_t region, uint8_t * kdata, size_t ksize, int num_masks, const struct find_search_mask *masks)
{
	uint16_t *end = (uint16_t *) (kdata + ksize - (num_masks * sizeof (uint16_t)));
	uint16_t *cur;
	for (cur = (uint16_t *) kdata; cur <= end; ++cur) {
		int matched = 1;
		int i;
		for (i = 0; i < num_masks; ++i) {
			if ((*(cur + i) & masks[i].mask) != masks[i].value) {
				matched = 0;
				break;
			}
		}

		if (matched)
			return cur;
	}

	return NULL;
}

unsigned long
Adler32 (unsigned char *buffer, long length)
{
	long cnt;
	unsigned long result, lowHalf, highHalf;

	lowHalf = 1;
	highHalf = 0;

	for (cnt = 0; cnt < length; cnt++) {
		if ((cnt % 5000) == 0) {
			lowHalf %= 65521L;
			highHalf %= 65521L;
		}
		lowHalf += buffer[cnt];
		highHalf += lowHalf;
	}

	lowHalf %= 65521L;
	highHalf %= 65521L;

	result = (highHalf << 16) | lowHalf;
	return result;
}

/**************************************************************
 LZSS.C -- A Data Compression Program
***************************************************************
	4/6/1989 Haruhiko Okumura
	Use, distribute, and modify this program freely.
	Please send me your improved versions.
		PC-VAN	  SCIENCE
		NIFTY-Serve PAF01022
		CompuServe  74050,1022

**************************************************************/
#define N		 4096			/* size of ring buffer - must be power of 2 */
#define F		 18				/* upper limit for match_length */
#define THRESHOLD 2				/* encode string into position and length
								 * if match_length is greater than this */
#define NIL	   N				/* index for root of binary search trees */

int
decompress_lzss (uint8_t * dst, uint8_t * src, uint32_t srclen)
{
	/*
	 * ring buffer of size N, with extra F-1 bytes to aid string comparison 
	 */
	uint8_t text_buf[N + F - 1];
	uint8_t *dststart = dst;
	uint8_t *srcend = src + srclen;
	int i, j, k, r, c;
	unsigned int flags;

	dst = dststart;
	srcend = src + srclen;
	for (i = 0; i < N - F; i++)
		text_buf[i] = ' ';
	r = N - F;
	flags = 0;
	for (;;) {
		if (((flags >>= 1) & 0x100) == 0) {
			if (src < srcend)
				c = *src++;
			else
				break;
			flags = c | 0xFF00;	/* uses higher byte cleverly */
		}						/* to count eight */
		if (flags & 1) {
			if (src < srcend)
				c = *src++;
			else
				break;
			*dst++ = c;
			text_buf[r++] = c;
			r &= (N - 1);
		}
		else {
			if (src < srcend)
				i = *src++;
			else
				break;
			if (src < srcend)
				j = *src++;
			else
				break;
			i |= ((j & 0xF0) << 4);
			j = (j & 0x0F) + THRESHOLD;
			for (k = 0; k <= j; k++) {
				c = text_buf[(i + k) & (N - 1)];
				*dst++ = c;
				text_buf[r++] = c;
				r &= (N - 1);
			}
		}
	}

	return dst - dststart;
}

int
kcache_decompress_kernel (void *compressedKernel, void *decompressedKernel, int *decompressed_size)
{
	struct compressed_kernel_header *kernel_header = (struct compressed_kernel_header *) compressedKernel;
	u_int32_t uncompressed_size, size;

	if (kernel_header->signature != __builtin_bswap32 ('comp')) {
		printf ("decompress_kernel: bad file magic\n");
		return -1;
	}

	if (kernel_header->signature == __builtin_bswap32 ('comp')) {
		if (kernel_header->compress_type != __builtin_bswap32 ('lzss')) {
			printf ("decompress_kernel: kernel compression is bad\n");
			return -1;
		}
	}

	uncompressed_size = __builtin_bswap32 (kernel_header->uncompressed_size);
	if (!decompressedKernel) {
		*decompressed_size = uncompressed_size;
		return 0;
	}

	size = decompress_lzss ((u_int8_t *) (decompressedKernel), &kernel_header->data[0], __builtin_bswap32 (kernel_header->compressed_size));

	if (uncompressed_size != size) {
		printf ("decompress_kernel: size mismatch from lzss: %x\n", size);
		return -1;
	}

	if (__builtin_bswap32 (kernel_header->adler32) != Adler32 (decompressedKernel, uncompressed_size)) {
		printf ("decompress_kernel: adler mismatch\n");
		return -1;
	}

	printf ("decompress_kernel: kernelcache decompressed to %p\n", decompressedKernel);

	*decompressed_size = size;
	return 0;
}

float
kcache_get_ios_version (void)
{
	float current_version = atof (kcache_get_darwin_version ());
	struct kernel_interval *interval = &intervals[0];
	while (interval->os_version != -1) {
		if (current_version >= interval->low_bound && current_version <= interval->high_bound)
			return interval->os_version;
		interval++;
	}
	err (-1, "failed to match kernel version, probably too new/old?");
	return 0;
}

char *
kcache_get_darwin_version (void)
{
	int i, len;
	char versbuf[20];
	char *versionpos;
	char *version_str = (char *) memmem (current_image.image, current_image.size,
										 "Darwin Kernel Version",
										 sizeof ("Darwin Kernel Version") - 1);
	if (!version_str)
		return NULL;

	versionpos = strnstr (version_str, "xnu-", strlen (version_str));
	for (i = 0, len = 4; len < 20; len++) {
		if (isdigit (versionpos[len]) || versionpos[len] == '.') {
			versbuf[i++] = versionpos[len];
			continue;
		}
		break;
	}
	if (versionpos[len - 1] == '.')
		i--;
	for (; len < 20; len++) {
		if (!isdigit (versionpos[len]))
			continue;
		break;
	}
	if (versionpos[len - 1] == '~') {
		versbuf[i++] = versionpos[len - 1];
		for (; len < 20; len++) {
			if (isdigit (versionpos[len])) {
				versbuf[i++] = versionpos[len];
				continue;
			}
			break;
		}
	}
	versbuf[i] = '\0';

	return strdup (versbuf);
}

/*
 * Fix MobileSubstrate entitlements.
 */
static int
kcache_ios7_mspatch (uint32_t region, uint8_t * kdata, size_t ksize)
{
	// 00 2F 15 D1 BA 69
	const struct find_search_mask search_masks[] = {
		{0xFFFF, 0x2F00},
		{0xFF00, 0xD100},
		{0xFFFF, 0x69BA},
	};

	uint16_t *insn = find_with_search_mask (region, kdata, ksize, sizeof (search_masks) / sizeof (*search_masks), search_masks);
	if (!insn)
		return 0;

	return (int) ((uintptr_t) insn - (uintptr_t) kdata) + 2;
}

static int
kcache_ios7_i_can_has_debugger (uint32_t region, uint8_t * kdata, size_t ksize)
{
	const struct find_search_mask search_masks[] = {
		{0xFFFF, 0x4478},		/* ADD r0, PC */
		{0xFFFF, 0xF8D0},		/* LDR r0, [r0, #val] */
		{0xFFF0, 0x0F20},		/* LDR r0, [r0, #val] cont */
		{0xFFFF, 0x4770},		/* BX lr */
	};

	uint16_t *insn = find_with_search_mask (region, kdata, ksize, sizeof (search_masks) / sizeof (*search_masks), search_masks);
	if (!insn)
		return 0;

	return (int) ((uintptr_t) insn - (uintptr_t) kdata) + 2;
}

static int
kcache_ios7_debugger_enabled (uint32_t region, uint8_t * kdata, size_t ksize)
{
	const struct find_search_mask search_masks[] = {
		{0xFFFF, 0x2800},		/* CMP r0, #0 */
		{0xFFFF, 0xBF18},		/* IT ne */
		{0xFFFF, 0x2001},		/* MOVne r0, #1 */
		{0xFFFF, 0xF8C1},		/* STR r0, [r1, #val] */
	};

	uint16_t *insn = find_with_search_mask (region, kdata, ksize, sizeof (search_masks) / sizeof (*search_masks), search_masks);
	if (!insn)
		return 0;

	return (int) ((uintptr_t) insn - (uintptr_t) kdata) + 2;
}

static int
kcache_ios7_tfp0 (uint32_t region, uint8_t * kdata, size_t ksize)
{
	// Find the task_for_pid function
	const uint8_t search[] = { 0x58, 0x46, 0x51, 0x46, 0x90, 0x47, 0x31, 0x46 };
	uint16_t *fn = memmem (kdata, ksize, search, sizeof (search));
	if (!fn)
		return 0;

	// Find the beginning of it
	uint16_t *fn_start = find_last_insn_matching (region, kdata, ksize, fn, insn_is_preamble_push);
	if (!fn_start)
		return 0;

	// Find where something is checked to be 0 (the PID check)
	int found = 0;
	uint16_t *current_instruction = fn_start;
	{
		const struct find_search_mask search_masks[] = {
			{0xFFF0, 0xF1B0},	/* CMP.w Rx, #0 */
			{0xFFFF, 0x0F00},
			{0xFFFF, 0xF000},	/* BEQ ... */
		};

		uint16_t *insn = find_with_search_mask (region, (uint8_t *) fn_start, 0x100, sizeof (search_masks) / sizeof (*search_masks), search_masks);
		if (insn)
			found = 1;
		current_instruction = insn;
	}

	if (!found)
		return 0;

	current_instruction += 2;

	return ((uintptr_t) current_instruction) - ((uintptr_t) kdata);
}

// NOP out the conditional branch here.
static uint32_t
kcache_ios7_vme (uint32_t region, uint8_t * kdata, size_t ksize)
{
	const struct find_search_mask search_masks[] = {
		{0xFFFF, 0xBF08},		/* IT eq */
		{0xFFF0, 0xF020},		/* BICeq Rx, Ry, #4 */
		{0xF0FF, 0x0004},
		{0xF8FF, 0x2800}		/* CMP Rx, #0 */
	};
	int found = 0;

	uint16_t *insn = find_with_search_mask (region, kdata, ksize, sizeof (search_masks) / sizeof (*search_masks), search_masks);
	if (!insn)
		return 0;

	// Find the next conditional branch
	found = 0;
	uint16_t *current_instruction = insn;
	while ((uintptr_t) current_instruction < (uintptr_t) insn + 0x100) {
		// The unconditional branch is to detect an already patched function and still return the right address.
		if (insn_is_b_conditional (current_instruction) || insn_is_b_unconditional (current_instruction)) {
			found = 1;
			break;
		}

		current_instruction += insn_is_32bit (current_instruction) ? 2 : 1;
	}
	if (!found)
		return 0;

	return ((uintptr_t) current_instruction) - ((uintptr_t) kdata);
}

// NOP out the conditional branch here.
static uint32_t
kcache_ios7_mount_common (uint32_t region, uint8_t * kdata, size_t ksize)
{
	const struct find_search_mask search_masks[] = {
		{0xFFFF, 0xF04F},		/* MOV Rx, #1 */
		{0xFF00, 0x0A00},
		{0xFFFF, 0xBF08},		/* IT eq */
		{0xFFF0, 0xF440},		/* ORReq Rx, Ry, #0x10000 */
		{0xFFFF, 0x3580}
	};

	uint16_t *insn = find_with_search_mask (region, kdata, ksize, sizeof (search_masks) / sizeof (*search_masks), search_masks);
	if (!insn)
		return 0;

	insn += 7;
	return ((uintptr_t) insn) - ((uintptr_t) kdata);
}

// Write this with a jump to the sandbox hook, then write a trampoline back to just after the jump you wrote here. Sandbox hook should look at the path in *(r3 + 0x14) and force
// it to be allowed if it is outside of /private/var/mobile, or inside of /private/var/mobile/Library/Preferences but not /private/var/mobile/Library/Preferences/com.apple*
// To force it to allow, *r0 = 0 and *(r0 + 0x4) = 0x18. If not, just call the original function via the trampoline.
static uint32_t
kcache_ios7_sb(uint32_t region, uint8_t* kdata, size_t ksize)
{
    // Find location of the "control_name" string.
    uint8_t* control_name = memmem(kdata, ksize, "control_name", sizeof("control_name"));
    if(!control_name)
        return 0;

    // Find a reference to the "control_name" string.
    uint16_t* ref = find_literal_ref(region, kdata, ksize, (uint16_t*) kdata, (uintptr_t)control_name - (uintptr_t)kdata);
    if(!ref)
        return 0;

    // Find the start of the function referencing "control_name"
    uint16_t* fn_start = ref;
    while(1)
    {
        fn_start = find_last_insn_matching(region, kdata, ksize, fn_start, insn_is_push);
        if(!fn_start)
            return 0;

        uint16_t registers = insn_push_registers(fn_start);
        // We match PUSH {R0, R1} as well to detect an already patched version.
        if((registers & (1 << 14)) != 0 || (registers & (1 << 0 | 1 << 1)) == (1 << 0 | 1 << 1))
            break;
    }

    return ((uintptr_t)fn_start) - ((uintptr_t)kdata);
}


static inline uint8_t *
kcache_off2pat_patch (int offset, uint8_t * patch, int bufsize, int patchsize)
{
	uint8_t *buffer = (uint8_t *) _xmalloc (bufsize);
	memcpy (buffer, current_image.image + offset, bufsize);
	memcpy (buffer, patch, patchsize);
	return buffer;
}

static void
kcache_ios7_dynapatch (void)
{
	int mspatch = 0, pedebugger = 0, debugger = 0, tfp0 = 0, vme = 0, mcommon = 0, sbox = 0;

	printf ("Patching kernel...\n");
	mspatch = kcache_ios7_mspatch (KERNEL_VMADDR, current_image.image, current_image.size);
	pedebugger = kcache_ios7_i_can_has_debugger (KERNEL_VMADDR, current_image.image, current_image.size);
	debugger = kcache_ios7_debugger_enabled (KERNEL_VMADDR, current_image.image, current_image.size);
	tfp0 = kcache_ios7_tfp0 (KERNEL_VMADDR, current_image.image, current_image.size);
	vme = kcache_ios7_vme (KERNEL_VMADDR, current_image.image, current_image.size);
	mcommon = kcache_ios7_mount_common (KERNEL_VMADDR, current_image.image, current_image.size);
	sbox = kcache_ios7_sb (KERNEL_VMADDR, current_image.image, current_image.size);

	if (!mspatch || !pedebugger || !debugger || !tfp0 || !vme || !mcommon || !sbox) {
		warn ("failed to find one or more patches, aborting!");
		return;
	}

	printf ("MobileSubstrate fix patch at %x.\n", mspatch);
	printf ("PE_I_can_has_debugger patch at %x.\n", pedebugger);
	printf ("debugger_enabled patch at %x.\n", debugger);
	printf ("task_for_pid 0 patch at %x.\n", tfp0);
	printf ("vm_map_enter patch at %x.\n", vme);
	printf ("mount_common patch at %x.\n", mcommon);
	printf ("sandbox patch at %x.\n", sbox);

	/*
	 * Write patches out. 
	 */
	uint8_t nop[] = { 0x00, 0xBF };
	uint8_t nop_nop[] = { 0xC0, 0x46, 0xC0, 0x46 };
	uint8_t movs_r0_imm1_bx_lr[] = { 0x01, 0x20, 0x70, 0x47 };
	uint8_t movs_r0_imm1_movs_r0_imm1[] = { 0x01, 0x20, 0x01, 0x20 };
	uint8_t sandbox_hack[] = {0x00, 0x21, 0x01, 0x60, 0x18, 0x21, 0x01, 0x71, 0x70, 0x47};
	uint8_t fixup[4];

	/*
	 * Convert the conditional branch into an unconditional one. 
	 */
	memcpy (fixup, current_image.image + vme, 4);
	fixup[1] = 0xE0;

	patch_list_initialize ();
	patch_list_add_patch ("MobileSubstrate entitlement fix", current_image.image + mspatch, kcache_off2pat_patch (mspatch, (uint8_t *) nop, 16, sizeof (nop)), 16);
	patch_list_add_patch ("PE_I_can_has_debugger", current_image.image + pedebugger, kcache_off2pat_patch (pedebugger, (uint8_t *) movs_r0_imm1_bx_lr, 16, sizeof (movs_r0_imm1_bx_lr)), 16);
	patch_list_add_patch ("Debugger enabled", current_image.image + debugger, kcache_off2pat_patch (debugger, (uint8_t *) movs_r0_imm1_movs_r0_imm1, 16, sizeof (movs_r0_imm1_movs_r0_imm1)), 16);
	patch_list_add_patch ("task_for_pid 0", current_image.image + tfp0, kcache_off2pat_patch (tfp0, (uint8_t *) nop_nop, 16, sizeof (nop_nop)), 16);
	patch_list_add_patch ("mount_common RW support", current_image.image + mcommon, kcache_off2pat_patch (mcommon, (uint8_t *) nop_nop, 16, sizeof (nop_nop)), 16);
	patch_list_add_patch ("vm_map_enter", current_image.image + vme, kcache_off2pat_patch (vme, (uint8_t *) fixup, 16, sizeof (fixup)), 16);
	patch_list_add_patch ("sandbox patch", current_image.image + sbox, kcache_off2pat_patch (sbox, (uint8_t *) sandbox_hack, 16, sizeof (sandbox_hack)), 16);
	patch_list_iterate ();
}

static void
kcache_patch_kernel (void)
{
	struct patch_list *head, *iter;
	int total_patches, i = 0, j = 0;
	double progress = 0.0;
	printf ("Patching kernel *NOW*...\n");

	if (patch_list_get_head (&head, &total_patches)) {
		warn ("failed to get patch list head\n");
		return;
	}

	/*
	 * Patch it!
	 */
	for (iter = head, i = 0; i < total_patches; iter = iter->next, i++) {
		for (j = 0; j < current_image.size; j++) {
			if (!memcmp (current_image.image + j, iter->patch.original, iter->patch.size)) {
				memcpy (current_image.image + j, iter->patch.patched, iter->patch.size);
				progress = ((i + 1) / (double) total_patches) * 100.0;
				printf ("%4.1f%% done. [(%d/%d) %-32.32s]\r", progress, i + 1, total_patches, iter->patch.name);
				fflush (stdout);
			}
		}
	}
	printf ("\n");
}

int
kcache_dynapatch (void)
{
	printf ("starting dynapatch...\n");

	switch ((int) kcache_get_ios_version ()) {
	case 7:					/* iOS 7. */
		kcache_ios7_dynapatch ();
		break;
	default:
		warn ("iOS %.1f not supported yet for kernel patcher", kcache_get_ios_version ());
		return -1;
	}

	kcache_patch_kernel ();
	return 0;
}

int
kcache_write_file (const char *filename)
{
	struct stat buf;
	FILE *fp = fopen (filename, "wb");

	if (!fp)
		return -ENOENT;
	if (stat (filename, &buf) > 0)
		return -ENOENT;

	fwrite ((void *) current_image.image, current_image.size, 1, fp);
	fclose (fp);

	free (current_image.image);
	current_image.image = NULL;
	current_image.size = 0;

	return 0;
}

int
kcache_map_file (const char *filename)
{
	struct stat buf;
#if USE_KERNELCACHE
	int decompressed_size = 0;
	void *decompressed;
#endif
	uint32_t kernel_entrypoint;
	loader_context_t ctx;

	FILE *fp = fopen (filename, "rb");

	if (!fp)
		return -ENOENT;
	if (stat (filename, &buf) > 0)
		return -ENOENT;

	current_image.image = (uint8_t *) _xmalloc (buf.st_size);
	current_image.size = buf.st_size;
	fread ((void *) current_image.image, buf.st_size, 1, fp);
	fclose (fp);

#if USE_KERNELCACHE				/* Just use MachOs directly. */
	if (kcache_decompress_kernel (current_image.image, NULL, &decompressed_size)) {
		free (current_image.image);
		return -1;
	}

	printf ("decompressed kernelcache size %d\n", decompressed_size);
	decompressed = _xmalloc (decompressed_size);
	if (kcache_decompress_kernel (current_image.image, decompressed, &decompressed_size)) {
		free (decompressed);
		return -1;
	}
	free (current_image.image);

	current_image.image = (uint8_t *) decompressed;
	current_image.size = decompressed_size;
#endif

	/*
	 * Verify the integrity of the kernelcache. 
	 */
#define mach_assert(x)				\
	do {							\
		if(!(x)) {					\
			warn(#x " failed");		\
			return -1;				\
		}							\
	} while(0);

	mach_assert (!macho_initialize (&ctx, (void *) current_image.image));
	mach_assert (!macho_set_vm_bias (&ctx, KERNEL_VMADDR));
	mach_assert (!macho_file_map (&ctx, 0, 0));
	mach_assert (!macho_get_entrypoint (&ctx, &kernel_entrypoint));
	mach_assert (kernel_entrypoint > KERNEL_VMADDR);
#undef mach_assert

	return 0;
}
