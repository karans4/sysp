#!/usr/bin/env python3
"""Catalog and extract files from Apple II DOS 3.3 .dsk images."""

import sys
import struct

# DOS 3.3 disk layout:
# 35 tracks, 16 sectors per track, 256 bytes per sector
# Total = 143360 bytes
# VTOC is at track 17, sector 0
# Catalog starts at the track/sector pointed to by VTOC

SECTOR_SIZE = 256
SECTORS_PER_TRACK = 16
TRACK_SIZE = SECTOR_SIZE * SECTORS_PER_TRACK

FILE_TYPES = {
    0x00: 'T',   # Text
    0x01: 'I',   # Integer BASIC
    0x02: 'A',   # Applesoft BASIC
    0x04: 'B',   # Binary
    0x08: 'S',   # Special (type S)
    0x10: 'R',   # Relocatable
    0x20: 'a',   # new A type
    0x40: 'b',   # new B type
}

def read_sector(data, track, sector):
    """Read a sector from the disk image."""
    offset = track * TRACK_SIZE + sector * SECTOR_SIZE
    return data[offset:offset + SECTOR_SIZE]

def catalog_disk(filename):
    """Read and print the catalog of a DOS 3.3 disk image."""
    with open(filename, 'rb') as f:
        data = f.read()

    if len(data) != 143360:
        print(f"Warning: file size {len(data)} != 143360 (expected DOS 3.3)")

    # Read VTOC at track 17, sector 0
    vtoc = read_sector(data, 17, 0)
    cat_track = vtoc[1]
    cat_sector = vtoc[2]
    dos_release = vtoc[3]
    volume = vtoc[6]

    print(f"Volume: {volume}")
    print(f"DOS release: {dos_release}")
    print(f"Catalog starts at T{cat_track} S{cat_sector}")
    print()
    print(f"{'Name':<33} {'Type':>4} {'Locked':>6} {'Size':>5} {'Addr':>6} {'Len':>6}")
    print("-" * 70)

    files = []

    # Walk catalog sectors
    while cat_track != 0:
        cat = read_sector(data, cat_track, cat_sector)
        # Next catalog sector
        next_track = cat[1]
        next_sector = cat[2]

        # Each catalog sector has 7 file entries starting at offset 0x0B
        for i in range(7):
            entry_offset = 0x0B + i * 0x23
            entry = cat[entry_offset:entry_offset + 0x23]

            # First byte is track of first T/S list sector
            # 0x00 = never used, 0xFF = deleted
            ts_track = entry[0]
            if ts_track == 0x00 or ts_track == 0xFF:
                continue

            ts_sector = entry[1]
            file_type_byte = entry[2]
            locked = bool(file_type_byte & 0x80)
            file_type = file_type_byte & 0x7F
            type_char = FILE_TYPES.get(file_type, f'?{file_type:02X}')

            # File name is bytes 3-32 (30 bytes), high bit set
            name_bytes = entry[3:33]
            name = ''.join(chr(b & 0x7F) for b in name_bytes).rstrip()

            # Sector count
            sector_count = entry[0x21] | (entry[0x22] << 8)

            # For binary files, read the first T/S list to get load address and length
            addr = None
            length = None
            if file_type == 0x04:  # Binary
                addr, length = get_binary_info(data, ts_track, ts_sector)

            addr_str = f"${addr:04X}" if addr is not None else ""
            len_str = f"${length:04X}" if length is not None else ""

            print(f"{name:<33} {type_char:>4} {'*' if locked else '':>6} {sector_count:>5} {addr_str:>6} {len_str:>6}")

            files.append({
                'name': name,
                'type': file_type,
                'type_char': type_char,
                'locked': locked,
                'ts_track': ts_track,
                'ts_sector': ts_sector,
                'sector_count': sector_count,
                'addr': addr,
                'length': length,
            })

        cat_track = next_track
        cat_sector = next_sector

    return data, files

def get_binary_info(data, ts_track, ts_sector):
    """Get load address and length from first data sector of a binary file."""
    # Read the T/S list sector
    ts_list = read_sector(data, ts_track, ts_sector)

    # Data sector pairs start at offset 0x0C
    first_data_track = ts_list[0x0C]
    first_data_sector = ts_list[0x0D]

    if first_data_track == 0:
        return None, None

    # First 2 bytes of first data sector = load address
    # Next 2 bytes = length
    first_sector = read_sector(data, first_data_track, first_data_sector)
    addr = first_sector[0] | (first_sector[1] << 8)
    length = first_sector[2] | (first_sector[3] << 8)

    return addr, length

def extract_file(data, file_info, output_filename=None):
    """Extract a file from the disk image."""
    ts_track = file_info['ts_track']
    ts_sector = file_info['ts_sector']

    if output_filename is None:
        output_filename = file_info['name'].strip().replace(' ', '_')

    # Collect all data sectors by walking T/S lists
    all_data = bytearray()

    while ts_track != 0:
        ts_list = read_sector(data, ts_track, ts_sector)
        next_ts_track = ts_list[1]
        next_ts_sector = ts_list[2]

        # Data sector pairs at offsets 0x0C, 0x0E, 0x10, ...
        for i in range(122):  # max 122 sector pairs per T/S list
            offset = 0x0C + i * 2
            d_track = ts_list[offset]
            d_sector = ts_list[offset + 1]

            if d_track == 0 and d_sector == 0:
                break

            sector_data = read_sector(data, d_track, d_sector)
            all_data.extend(sector_data)

        ts_track = next_ts_track
        ts_sector = next_ts_sector

    # For binary files, strip the 4-byte header (addr + length) and trim to length
    if file_info['type'] == 0x04 and len(all_data) >= 4:
        addr = all_data[0] | (all_data[1] << 8)
        length = all_data[2] | (all_data[3] << 8)
        raw_data = all_data[4:4 + length]
        print(f"Extracted binary: load addr=${addr:04X}, length=${length:04X} ({length} bytes)")

        with open(output_filename, 'wb') as f:
            f.write(raw_data)
        print(f"Wrote {len(raw_data)} bytes to {output_filename}")
        return addr, raw_data
    else:
        with open(output_filename, 'wb') as f:
            f.write(all_data)
        print(f"Wrote {len(all_data)} bytes to {output_filename}")
        return None, all_data

if __name__ == '__main__':
    if len(sys.argv) < 2:
        print(f"Usage: {sys.argv[0]} <disk.dsk> [extract <filename> [output]]")
        sys.exit(1)

    disk_file = sys.argv[1]
    data, files = catalog_disk(disk_file)

    if len(sys.argv) >= 4 and sys.argv[2] == 'extract':
        target = sys.argv[3]
        output = sys.argv[4] if len(sys.argv) >= 5 else None
        for f in files:
            if f['name'].strip() == target:
                print()
                extract_file(data, f, output)
                break
        else:
            print(f"\nFile '{target}' not found on disk")
