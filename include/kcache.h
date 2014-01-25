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

#ifndef __KCACHE_H
#define __KCACHE_H

float	kcache_get_ios_version (void);
char*	kcache_get_darwin_version (void);
int		kcache_map_file (const char *filename);
int		kcache_dynapatch (void);
int		kcache_write_file (const char *filename);

#endif /* __KCACHE_H */