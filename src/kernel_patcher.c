/*-
 * Copyright 2013, winocm <winocm@icloud.com>
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

int
main (int argc, char *argv[])
{
	if (argc != 3) {
		printf ("usage: %s [in] [out]\n", argv[0]);
		return -1;
	}

	assert (kcache_map_file (argv[1]) == 0);
	printf ("xnu-%s\n", kcache_get_darwin_version ());
	printf ("iOS %.1f\n", kcache_get_ios_version ());
	assert (kcache_dynapatch () == 0);
	assert (kcache_write_file (argv[2]) == 0);

	return 0;
}
