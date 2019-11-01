#!/usr/bin/python
#
# adisk is (C) Dan Hovang 2008
# Distribution permitted under GPLv2 - http://www.gnu.org/licenses/gpl-2.0.html
#
# Requirements: decent version of Python
#
# Stuff that maybe could be added:
#
#  Extraction of the LSEG file (what's the use?)
#  Checking of consistency / repairing (that's a lot of work ..)
#  Make fuse interface
#  XPK interface (through 68k emulator?)
#

import re
import os
import sys
import stat
import copy
import time
import array
import getopt
import string
import struct
import traceback

debug = 0

class rdsk_exception(BaseException):

    def __init__(self, msg):
        self.msg = msg


    def __str__(self):
        ret = traceback.print_tb(sys.exc_info()[2])
        if self.msg:
            ret += "\n" + self.msg
        return ret

        
    def get_msg(self):
        return self.msg


class rdsk_checksum_exception(BaseException):

    def __init__(self, blockno, filename = "<no file>"):
        self.blockno = blockno
        self.filename = filename

    

# Check the checksum
# The sum of all 32 bit words (little endian) should equal zero

def rdsk_checksum(data):

    if len(data) != 512:
        raise rdsk_exception("Invalid block length %d" % len(data))

    sum = 0
    ix = 0
    while ix != 512:

        s1 = (ord(data[ix + 0]) << 8) | ord(data[ix + 1])
        s2 = (ord(data[ix + 2]) << 8) | ord(data[ix + 3])
        t = (s1 << 16) | s2
        sum += t
        ix += 4

    sum &= 0xffffffff
    if sum == 0:
        return 1
    else:
        return 0


# Return the 32 bit checksum for given block
# The word at chksum_offset will not be included in the calculation
    
def rdsk_calc_chksum(data, chksum_offset = 20):

    if len(data) != 512:
        raise rdsk_exception("Invalid block length %d" % len(data))

    sum = 0
    ix = 0
    while ix != 512:

        # Checksum is stored at word 5 (20 bytes) into data
        # don't include it in checksum
        
        if ix != chksum_offset:
            s1 = (ord(data[ix + 0]) << 8) | ord(data[ix + 1])
            s2 = (ord(data[ix + 2]) << 8) | ord(data[ix + 3])
            t = (s1 << 16) | s2
            sum += t

        ix += 4

    return (-sum) & 0xffffffff

# Convert amiga timestamp (days, mins, ticks tuple) to string.
# Amiga stores time since 1 jan 1978 and Unix from 1 jan 1970.
# This makes for a 0x0f0c3f00 (or 252460800) seconds difference.

def amiga_timestamp(dmt):

    secs = (dmt[0] * 24 * 60 * 60) + (dmt[1] * 60)
    secs += 252460800

    return time.gmtime(secs)


def dump(data):

    print "0x000: ",
    pos = 0
    a = ""
    while pos < 512:
        h = ord(data[pos])
        print "%02x" % h,
        if h >= 0x20 and h <= 0x7e:
            a += data[pos]
        else:
            a += "."
        if pos & 0x0f == 0x0f and (pos + 1) < 512:
            print "%s\n0x%03x: " % (a, pos + 1),
            a = ""
        pos += 1
    if len(a) > 0:
        print "%s" % a
    else:
        print



class ffs_file:

    def __init__(self, fs, blkno, data = None, path = None):

        if path is None:
            path = ""

        # Read the header block
        
        self.fs = fs
        self.blkno = blkno
        if not data:
            data = fs.part.read_block(blkno, True)

        self.path = path
            
        # 0  type (2)
        # 1  header_key
        # 2  high_seq
        # 3
        # 4  first data
        # 5  checksum
            
        fmt = ">IIIIII"
        pos = 0
        size = 6 * 4
        r1 = struct.unpack(fmt, data[pos: pos + size])
        pos += size

        if r1[0] != 2:
            msg == "Not a file header block %08x" % blkno
            raise rdsk_exception(msg)
        
        # Data block pointers

        cnt = (512 - (200 + 24)) / 4
        fmt = ">" + ("I" * cnt)
        size = cnt * 4
        dbp = struct.unpack(fmt, data[pos : pos + size])
        self.data_blocks = dbp
        #pos += size

        # 0  unused
        # 1  UID
        # 2  GID
        # 3  protect
        # 4  size
        # 5  comm len
        # 6  comment
        # 7  unused
        # 8  days
        # 9  mins
        # 10 ticks
        # 11 namelen
        # 12 name
        # 13 unused (byte)
        # 14 unused (long)
        # 15 real_entry
        # 16 next_link
        # 17 unused (5 words)
        # 22 hash_chain
        # 23 parent
        # 24 extension
        # 25 sec_type
        
        
        fmt = ">" + "IHHIIB79s12sIIIB30sBIIIIIIIIIIII"
        pos = 512 - 200
        r2 = struct.unpack(fmt, data[pos : ])
        pos += size

        self.created = r2[8:10]
        
        self.name = r2[12][0:r2[11]]
        self.full_path = self.name
        if self.path != "":
            self.full_path = self.path + "/" + self.full_path
        self.comment = r2[6][0:r2[5]]
        self.size = r2[4]
        self.hash_chain = r2[22]
        self.parent = r2[23]
        self.extension = r2[24]
        self.st_file = r2[25]
        if not self.st_file == 0xfffffffd:
            msg = "Bad sec_type, expecting 0xfffffffd got %08x" % self.st_file
            raise rdsk_exception(msg)
        self.inf = ""
        self.data = None
        self.scan()


    def info(self, level = 0):

        pre = (" " * level) * 2
        post = (" " * (9 - level)) * 2
        if self.scan:
            scan = "-"
        else:
            scan = "-"
        return "%08x %10d  %s%-40s%s %s %s\n" % \
            (self.blkno, self.size, pre, self.name, post, scan, self.comment)


    #
    # Examine first data block of file to try and determine file type.
    # Mainly .. Determine if XPK compressed file or not.
    #

    def scan(self):

        # Read first data block of file ..

        fb = self.fs.part.read_block(self.data_blocks[-1])

        tup = struct.unpack(">4sI4sI", fb[0:16])
        if tup[0] == "XPKF":
            self.xpk = 1
            self.scan = 0
            self.xpktype = tup[2]
            self.xpkorigsize = tup[3]

            self.xpkinitial = fb[16:32]
            flags = ord(fb[32])
            fi = ""
            self.xpkflags = flags
            if flags & 0x01:
                fi += "LONGHEADERS "
            elif flags & 0x02:
                fi += "PASSWORD "
            elif flags & 0x04:
                fi += "EXTHEADER "
            fi = fi[:-1]
            
            self.xpkhchk = ord(fb[33])
            self.xpksubv = ord(fb[34])
            self.xpkmasv = ord(fb[35])

            # Calc header checksum
            
            sum = 0
            for b in fb[0:36]:
                sum ^= ord(b)
            if sum == 0:
                self.xpkhchkok = 1
                hchk = "ok"
            else:
                self.xpkhchkok = 0
                hchk = "bad!"
            
            if tup[3] > 0:
                self.xpkratio = 100 - (100 * tup[1] / tup[3])
            else:
                self.xpkratio = 0

            self.inf = " XPK header: Flags 0x%02x (%s) HChk 0x%02x (%s)" \
                % (self.xpkflags, fi, self.xpkhchk, hchk)
        else:
            self.scan = 1
            self.inf = ""
            self.xpk = 0
            self.xpktype = ""
            self.xpkratio = 0
            self.xpkorigsize = 0


    #
    # Get full file and return as byte array (string)
    #
    
    def get(self, force_reread = 0):

        if (not self.data is None) and force_reread == 0:
            return self.data
        
        errmsg = "Error when reading file '%s' (hdrblk 0x%08x):\n" \
                 % (self.name, self.blkno)

        #print "Reading file %s, size %d bytes" % (self.name, self.size)
        
        ret = ""

        # Read data blocks

        blk = len(self.data_blocks) - 1
        db = self.data_blocks[blk]
        while db:
        #    print "reading data from block %08x (%d to %d)" % \
        #        (db, len(ret), len(ret) + 512)
            ret += self.fs.part.read_block(db)
            blk -= 1
            if blk < 0:
                break
            db = self.data_blocks[blk]

        # Do extensions

        ext = self.extension
        #print "extension block %08x" % ext
        cnt = (512 - 200 - 24) / 4
        fmt = ">" + ("I" * cnt)
        while ext != 0:
            ed = self.fs.part.read_block(ext, True)

            tup = struct.unpack(">I", ed[0:4])
            if tup[0] != 16:
                msg = errmsg + \
                    "Block %08x is not an extension block\n" % ext
                raise rdsk_exception(msg)

            # TODO check type == 16
            tup = struct.unpack(">II", ed[-8:])            
            raw = struct.unpack(fmt, ed[24 : 512 - 200])

            blk = len(raw) - 1
            db = raw[blk]
            while db:
                ret += self.fs.part.read_block(db)
                blk -= 1
                if blk < 0:
                    break
                db = raw[blk]

            ext = tup[0]

        if self.size > len(ret):
            msg = errmsg + \
                  "Data block chain, size %d got only %d\n" \
                  % (self.size, len(ret))
            raise rdsk_exception(msg)

        ret = ret[:self.size]
        self.data = ret
        return ret


    def is_file(self):
        return 1


    def is_dir(self):
        return 0


    def xpk_analyze(self):

        # TODO .. this does not work
        # XPK should really be abstracted

        return

        if not self.xpk:
            return

        # Get file data

        d = self.get()

        # Get XPK header
        
        fh = d[0:36]
        d = d[36:]
        
        while 1:
        
            if self.xpkflags & 0x01:
                hlen = 12
                hfmt = ">BBHII"
            else:
                hlen = 8
                hfmt = ">BBHHH"

            if len(d) < hlen:
                msg = "Unexpected end of XPK file, %s" % self.name
                print msg
                break
                
            hd = d[0:hlen]
            hdr = struct.unpack(hfmt, hd)
            d = d[hlen:]

            sum = 0
            for b in hd:
                sum ^= ord(b)

            if sum != 0:
                msg = "Bad XPK header checksum in file %s" % self.name
                # TODO
                return
                #raise rdsk_exception(msg)

            type = hdr[0]
            # hdr[1] == hsum
            cchk = hdr[2]
            clen = hdr[3]
            ulen = hdr[4]

            chunk = d[:clen]
            d = d[clen:]

            if type == 0x0f:
                break


            

class ffs_dir:

    def __init__(self, fs, blkno, data = None, scanctx = None, path = None):

        if path is None:
            path = ""

        self.fs = fs
        self.blkno = blkno
        self.path = path
        self.size = 0
        if not data:
            data = fs.part.read_block(blkno, True)

        r1 = struct.unpack(">IIII", data[0:16])
        if r1[0] != 2:
            print
            dump(data)
            msg = "Not a FFS directory block, bad type field (expecting 2)"
            raise rdsk_exception(msg)
            
        # 0
        # 1
        # 2  user id
        # 3  group id
        # 4  protect
        # 5
        # 6  comm len
        # 7  comment
        # 8  unused
        # 9  days
        # 10 mins
        # 11 ticks
        # 12 namelen
        # 13 name
        # 14 unused (byte)
        # 15 unused (long)
        # 16 unused (long)
        # 17 next_link
        # 18 unused (5 words)
        # 23 hash_chain
        # 24 parent
        # 25 ext
        # 26 sec_type
            
        fmt = ">HHHHIIB79s12sIIIB30sBIIIIIIIIIIII"
        pos = 512 - 200
        r2 = struct.unpack(fmt, data[pos : ])
        if r2[26] != 2: # ST_USERDIR
            print
            dump(data)
            msg = "Not a FFS directory block, bad sec_type field (expecting 2)"
            raise rdsk_exception(msg)

        self.created = r2[9:11]
        self.name = r2[13][0:r2[12]]
        self.comment = r2[7][0:r2[6]]
        self.hash_chain = r2[23]
        self.parent = r2[24]
        self.full_path = self.name
        if self.path != "":
            self.full_path = self.path + "/" + self.full_path

        # Recurse ..

        cnt = (512 - (200 + 24)) / 4
        fmt = ">" + ("I" * cnt)
        ht = struct.unpack(fmt, data[24 : 24 + cnt * 4])

        next_path = self.name
        if self.path != "":
            next_path = self.path + "/" + next_path
        
        self.nodes = self.fs.traverse_hash(ht, scanctx, next_path)
        self.inf = ""
        

    def info(self, level = 0, incl_nodes = True):
        pre = (" " * level) * 2
        post = (" " * (9 - level)) * 2
        ret = "%08x             %s%-40s%s - %s\n" % \
            (self.blkno, pre, self.name, post, self.comment)
        if incl_nodes:
            for n in self.nodes:
                ret += n.info(level + 1)
        return ret


    def is_file(self):
        return 0


    def is_dir(self):
        return 1


    @staticmethod
    def trace_path(part, parent_blkno):
        data = part.read_block(parent_blkno)
        hdr = struct.unpack(">II", data[0:8])
        tail = struct.unpack(">III", data[500:512])
        if hdr[0] != 2:
            print
            dump(data)
            msg = "Bad parent type, expecting 2, got %08x" % hdr[0]
            raise rdsk_exception(msg)
        if tail[2] == 1: # ST_ROOT
            rootblock = part.fs.rootblock - part.loblk
            if parent_blkno != rootblock:
                print "Block %08x" % parent_blkno
                dump(data)
                data = part.read_block(rootblock)
                print "Block %08x" % rootblock
                dump(data)
                msg = "Two rootblocks on %08x and %08x?" % \
                    (parent_blkno, rootblock)
                raise rdsk_exception(msg)
            print part.fs.volname + " (Volume)"
        elif tail[2] == 2: # ST_USERDIR
            d = ffs_dir(part.fs, parent_blkno, data)
            print d.info(0, False),
            dump(data)
            ffs_dir.trace_path(part, d.parent)
        else:
            print
            dump(data)
            msg = "Bad parent sec_type, expecting 1 or 2, got %08x" % hdr[0]
            raise rdsk_exception(msg)


    
    
class ffs_partition:

    fs_type = "FFS"

    def __init__(self, part):

        self.part = part

        # Calculate location of rootblock

        # (Highcyl - Lowcyl) + 1
        nc = part.raw[36] - part.raw[35] + 1
        hk = (nc * part.rdsk.cylblks) - 1
        rb = (int(part.raw[32] + hk) / 2) + (part.raw[35] * part.rdsk.cylblks)
        self.rootblock = rb

        part.rdsk.log("Partition %d, root block at %d (%08x)\n" %
                      (0, rb, rb * 512), 4)

        # Read partition root block
        
        rdata = part.rdsk.read_block(rb, True)

        # 0  type (2)
        # 1  header_key (not used - always 0)
        # 2  high_seq (not used - always 0)
        # 3  hash table size (number of longs)
        # 4  first_data (not used)
        # 5  checksum

        # Unpack first piece of rootblock to get hash table size
        
        fmt = ">IIIIII"
        pos = 0
        r1 = struct.unpack(fmt, rdata[pos:pos + 24])
        pos += 24
        
        if r1[0] != 2:
            msg = "Partition %d: invalid rootblock at 0x%08x\n" \
                  "Block type not 0x00000002 (found 0x%08x)\n" \
                  % (part.partno, self.rootblock, r1[0])
            raise rdsk_exception(msg)

        # Create format for hash table

        htsize = r1[3]
        fmt = ">"
        fmt += "I" * htsize
        self.htsize = htsize

        # Get hash table

        hts = htsize * 4
        ht = struct.unpack(fmt, rdata[pos:pos + hts])
        pos += hts

        fmt = ">"

        # 0  bitmap flag
        # 1  bitmap pages (25 words)
        # 26 bitmap extension
        # 27 days
        # 28 mins
        # 29 ticks

        fmt += "I" + ("I" * 25) + "IIII"

        # 30 namelen
        # 31 name
        # 32 unused (0)
        # 33
        # 34
        # 35 days
        # 36 mins
        # 37 ticks
        # 38 created days
        # 39 created mins
        # 40 created ticks
        # 41
        # 42
        # 43
        # 44 sec_type (1)

        fmt += "B30sBIIIIIIIIIIII"
        r2 = struct.unpack(fmt, rdata[pos:512])

        if r2[44] != 1:
            msg = "Partition %d: invalid rootblock at 0x%08x\n" \
                  "Sector type not 0x00000001 (found 0x%08x)\n" \
                  % (part.partno, self.rootblock, r2[44])
            raise rdsk_exception(msg)

        if r2[0] == 0xffffffff:
            self.valid = True
        else:
            self.valid = False

        self.rootblock1 = r1
        self.rootblock2 = r2
        self.hashtable = ht
        self.volname = r2[31][0:r2[30]]

        part.rdsk.log("Found partition %d at %08x (ofs %08x)\n" \
                      "Rootblock at %08x (ofs %08x), scanning ..\n" \
                      % (part.partno, part.blkno, part.blkno * 512,
                         self.rootblock, self.rootblock * 512), 4)

        self.nodes = None


    def find_all_nodes(self):
        
        # Travese nodes on this partition

        scanctx = []
        self.nodes = self.traverse_hash(self.hashtable, scanctx, "")

        self.part.rdsk.log("Total %d files and directories found\n" \
                               % len(scanctx), 4)
        self.node_list = scanctx


    #
    # Scan hash table in rootblock or directory block. Return a list of all
    # nodes found, including traversing the hash chain.
    #

    def traverse_hash(self, ht, scanctx = None, path = None):

        ix = 0
        ret = []
        for entry in ht:
            while entry != 0:
                node = None

                data = self.part.read_block(entry, True)
                fmt = ">" + ("I" * 128)
                raw = struct.unpack(fmt, data)

                if raw[0] != 2:
                    msg = "Bad block, found %08x on block %08x (expected 0x02)" % (raw[0], entry)
                    raise rdsk_exception(msg)
                else:
                    st = raw[127]
                    if st == 2:             # ST_USERDIR
                        node = ffs_dir(self, entry, data, scanctx, path)
                    elif st == 0xfffffffd:  # ST_FILE
                        node = ffs_file(self, entry, data, path)
                    else:                   # Unknown sector type
                        msg = "Bad block, found %08x on block %08x" % (st, entry)
                        raise rdsk_exception(msg)

                    if node:
                        ret.append(node)
                    if not scanctx is None:
                        scanctx.append(node)

                # Walk down the hash chain (if any)

                if node:
                    entry = node.hash_chain

            ix += 1

        return ret


    #
    # Read a file on this partition
    #

    def get_file(self, blkno):
        if not self.nodes:
            self.find_all_nodes()
        n = ffs_file(self, blkno)
        return n.get()


    def get_a_list_of_files(self, regexp):
        if not self.nodes:
            self.find_all_nodes()
        mo = re.compile(regexp)
        ret = []
        for n in self.node_list:
            if mo.search(n.full_path):
                ret.append(n)

        return ret


    # Scan for files on this partition (incl unlinked)

    def scan(self, rex):
        r = re.compile(rex)
        block = 0
        while block < (self.part.hiblk - self.part.loblk):
            data = self.part.read_block(block)
            tp = struct.unpack(">I", data[0:4])[0]
            if tp == 2: # T_HEADER
                sec_tp = struct.unpack(">I", data[512-4:512])[0]
                if sec_tp == 0xfffffffd: # ST_FILE
                    f = ffs_file(self, block, data)
                    if r.match(f.name):
                        print f.info(),
                        ffs_dir.trace_path(self.part, f.parent)

            block += 1


class pfs_partition:

    fs_type = "PFS"

    def __init__(self, part):
        self.part = part


    
class partition:

    def __init__(self, blkno, rdsk, partno):

        # Read partition block
        
        self.rdsk = rdsk
        self.partno = partno
        self.blkno = blkno
        self.valid = None
        data = rdsk.read_block(blkno, True)

        # Get partition blocks

        # 0  magic (PART)
        # 1  size (0x40)
        # 2  checksum
        # 3  host id
        # 4  next
        # 5  flags
        # 6  reserved (2 words)
        
        fmt = ">4sIIIIIII"

        # 8  dev flags
        # 9  drive name length
        # 10 drive name
        
        fmt = fmt + "IB31s"

        # 11 reserved (15 words)

        fmt = fmt + "IIIIIIIIIIIIIII"

        # 26 size of vector
        # 27 size of blocks (longs, 128 == 512 bytes)
        # 28 sec org (should be 0)
        # 29 surfaces
        # 30 sectors/block
        # 31 blocks/track
        # 32 no reserved blocks at beginning (usually 2, minimum 1)
        # 33 preallocated blocks and end of partition
        # 34 interleave
        # 35 low cyl (inclusive)
        # 36 high cyl (inclusive)
        # 37 num buf
        # 38 buf mem type
        # 39 max transfer
        # 40 mask
        # 41 boot prio
        # 42 dos type
        # 43 baud
        # 44 control
        # 45 bootblocks

        fmt = fmt + "IIIIIIIIIIIIIIII4sIII"

        # 46 reserved (12 words)

        fmt = fmt + (12 * "I")

        # Unpack the block

        raw = struct.unpack(fmt, data[0:256])
        self.raw = raw

        # Check magic

        if raw[0] != 'PART':
            msg = "Bad magic, expected PART on block %d" % blkno
            raise rdsk_exception(msg)
        else:
            self.rdsk.log("Found magic PART on block %d\n" % blkno, 4)

        # Get some data

        self.surfaces = raw[29]
        self.sectors_per_block = raw[30]
        self.blocks_per_track = raw[31]
        self.reserved = raw[32]
        self.locyl = raw[35]
        self.hicyl = raw[36]
        self.bootprio = raw[41]
        self.bootblocks = raw[45]

        # Compute some stuff

        self.loblk = self.locyl * self.rdsk.cylblks
        self.loofs = self.loblk * self.rdsk.blocksize

        self.hiblk = self.hicyl * self.rdsk.cylblks
        self.hiofs = self.hiblk * self.rdsk.blocksize

        # Next partition block location (used by callee)

        self.next = self.raw[4]

        # Check what type of file system this partiotion has; read bootblock

        bb = self.read_block(0)

        # Check for DOS1

        self.fs = None

        if bb[0] == 'D' and bb[1] == 'O' and bb[2] == 'S':
            self.rdsk.log("FFS bootblock found\n", 4)
            self.fs = ffs_partition(self)
        elif bb[0] == 'P' and bb[1] == 'F' and bb[2] == 'S':
            self.rdsk.log("PFS bootblock found\n", 4)
            self.fs = pfs_partition(self)
        else:
            self.rdsk.log("No bootblock found\n", 4)


    def part_info(self):

        p = self.raw

        if self.fs:
            type = self.fs.fs_type
        else:
            type = "unknown"

        #type = "DOS"
        #if ord(p[42][3]) == 1:
        #    type += "1 (FFS)"
        #else:
        #    type += "0 (OFS)"

        if self.valid is None:
            val = "unknown"
        else:
            if self.valid:
                val = "yes"
            else:
                val = "no"
        
        ret = \
            "Partition      %s\n" \
            "Sect per blk   %d\n" \
            "Blk per trk    %d\n" \
            "Lo cyl         %-5d (blk %08x (%7d) ofs %08x)\n" \
            "Hi cyl         %-5d (blk %08x (%7d) ofs %08x)\n" \
            "Res blks start %d\n" \
            "Boot blocks    %08x\n" \
            "DOS type       %s\n" \
            "Valid          %s\n" \
            % (p[10][0:p[9]],
               self.sectors_per_block,
               self.blocks_per_track,
               p[35], self.loblk, self.loblk, self.loofs,
               p[36], self.hiblk, self.hiblk, self.hiofs,
               self.reserved,
               self.bootblocks,
               type,
               val)

        return ret


    #
    # Create a string with readable information on this partition
    #

    def info(self):

        p = self.raw

        type = "DOS"
        if ord(p[42][3]) == 1:
            type += "1 (FFS)"
        else:
            type += "0 (OFS)"

        if self.valid is None:
            val = "unknown"
        else:
            if self.valid:
                val = "yes"
            else:
                val = "no"
        
        ret = \
            "Partition      %s\n" \
            "Lo cyl         %-5d (blk 0x%06x/%7d ofs %08x)\n" \
            "Hi cyl         %-5d (blk 0x%06x/%7d ofs %08x)\n" \
            "Res blks start %d\n" \
            "DOS type       %s\n" \
            "Rootblock      %d (ofs %08x)\n" \
            "Volume name    %s\n" \
            "Valid          %s\n" \
            "Hash size      %d entries\n" \
            % (p[10][0:p[9]],
               p[35], self.loblk, self.loblk, self.loofs,
               p[36], self.hiblk, self.hiblk, self.hiofs,
               p[32],
               type,
               self.rootblock, self.rootblock * 512,
               self.volname,
               val,
               self.htsize)

        return ret
        
        ret += "\n"
        ret += "Size        Name\n"
        ret += "----------  ----------------------------------------\n"
        
        for n in self.nodes:
            ret += n.info()
        
        return ret


    #
    # Read a block in this partition (offset by partition start)
    #

    def read_block(self, blkno, chksum = False):

        # Check so that read is in partition

        if blkno > self.hiblk:
            msg = "Read byond end of partition %08x" % blkno
            raise rdsk_exception(msg)

        return self.rdsk.read_block(blkno + self.loblk, chksum)


    #
    # Read a file on this partition
    #

    def get_file(self, blkno):
        return self.fs.get_file(blkno)


    def get_a_list_of_files(self, regexp):
        return self.fs.get_a_list_of_files(regexp)        


    #
    # Store this partition into a file
    #

    def save_as_file(self, filename):

        if False and os.path.exists(filename):
            print "File %s exists" % filename
            sys.exit(1)
            
        f = open(filename, "w")
        try:
            blk = 0
            count = 0
            bytes = 0
            while blk <= self.hiblk:

                data = self.rdsk.read_block(blk + self.loblk)
                f.write(data)
                
                blk += 1
                count += 1
                bytes += 512

        finally:
            f.close()

        print "Stored %d blocks/%d bytes to %s" % \
            (count, bytes, filename)


    def scan(self, rex):
        self.fs.scan(rex)


class fshd_block:

    def __init__(self, data, rdsk):
        self.rdsk = rdsk
        self.data = data
        s = ">IIIIIIIIIIIIIIIIIIII"
        hdr = struct.unpack(s, data[0:80])

        # 0  id (FSHD)
        # 1  size in longs (64)
        # 2  checksum
        # 3  host ID
        # 4  next (FSHD block)
        # 5  flags
        # 6  RESERVED
        # 7  RESERVED
        # 8  DosType
        # 9  Version
        # 10 PathFlags
        # 11 Type (0)
        # 12 Task (0)
        # 13 Lock (0)
        # 14 Handler (0)
        # 15 StackSize (0)
        # 16 Priority (0)
        # 17 Startup msg (0)
        # 18 SegListBlock
        # 19 GlobalVec

        blk = hdr[18] # LSEG blocks
        lseg = []
        if blk > 0:
            while True:
                data = self.rdsk.read_block(blk)
                rdsk_checksum(data)
                hdr = struct.unpack(">4sIIII", data[0:20])
                # 0  id (LSEG)
                # 1  size (in longs)
                # 2  checksum
                # 3  hostID (often 7)
                # 4  next (or -1 for the last)
                if hdr[0] != 'LSEG':
                    print "WARNING: broken LSEG chain in FSHD blocks"
                    if len(lseg) > 0:
                        print "Last good block was %08x" % lseg[-1][0]
                        dump(lseg[-1][1])
                        print "Broken block is %08x" % blk
                        dump(data)
                    break
                lseg.append((blk, data))
                blk = hdr[4] # Next
                if blk == 0xffffffff:
                    break



class rdsk_disk:

    #
    # Constructor
    #
    
    def __init__(self, file_name, dbglvl = 3):

        self.dbglvl = dbglvl
        self.file_name = file_name
        self.offset = 0

        # Array with all partitions

        self.part = []

        # Open image file

        self.flip = 0

        self.log("Trying to open RDSK image file '%s'\n" % file_name, 4)

        st = os.stat(file_name)
        self.raw_size = st[stat.ST_SIZE]
        
        f = open(file_name, "r")
        self.file = f

        # Locate RDSK block

        self.rdsk_pos = self.scan_rdsk()
        self.fshd = self.scan_fshd()

        print "Found %d FSHD blocks" % len(self.fshd)

        # 0  id, (RDSK)
        # 1  size
        # 2  checksum
        # 3  host id
        # 4  block size
        # 5  flags
        # 6  bad block list
        # 7  partition list
        # 8  file sys hdr list
        # 9  drive init code
        
        fmt = ">4sIIIIIIIII"

        # 10 reserved (6 words)

        fmt = fmt + "IIIIII"

        # 16 cylinders
        # 17 sectors
        # 18 heads
        # 19 interleave
        # 20 parking zone
        
        fmt = fmt + "IIIII"

        # 21 reserved (3 words)

        fmt = fmt + "III"

        # 24 write pre comp
        # 25 reduced write
        # 26 step rate
        # 27 reserved (5 words)

        fmt = fmt + "IIIIIIII"

        # 32 rdb_lo
        # 33 rdb_hi
        # 34 lo cyl
        # 35 hi cyl
        # 36 cyl blocks
        # 37 auto park seconds
        # 38 hi rdsk block
        # 39 reserved

        fmt = fmt + "IIIIIIII"

        # 40 vendor
        # 41 product
        # 42 disk revision
        # 43 controller vendor
        # 44 controller product
        # 45 controller revision
        # 46 reserved (10 words)
        
        fmt = fmt + "8s16s4s8s16s4sIIIIIIIIII"
        self.rdsk = struct.unpack(fmt, self.rdsk_raw[0:256])

        self.fshdrlist = self.rdsk[8]
        self.driveinit = self.rdsk[9]
        self.blocksize = self.rdsk[4]
        self.cylinders = self.rdsk[16]
        self.sectors = self.rdsk[17]
        self.heads = self.rdsk[18]

        self.rdblo = self.rdsk[32]
        self.rdbhi = self.rdsk[33]
        self.locyl = self.rdsk[34]
        self.hicyl = self.rdsk[35]

        #self.cylblks = self.sectors * self.heads
        self.cylblks = self.rdsk[36]
        self.total_size = self.cylblks * self.cylinders * self.blocksize

        # Get all PART blocks
        
        p = self.rdsk[7]
        pno = 0
        while p < 2^31:
            part = partition(p, self, pno)
            self.part.append(part)

            # Get next partition block
            
            p = part.next
            pno += 1

    #
    # Locate RDSK block
    #

    def scan_rdsk(self, max_block = 32):

        valid = 0
        offset = 0

        while True:

            # Read first block (RDSK block)
        
            self.log("Examining block %d\n" % (offset), 4)
            rdsk = self.read_block(offset)

            # Check RDSK block magic word and determine byte order

            if str(rdsk[0:4]) == "RDSK":

                if rdsk_checksum(rdsk):
                    self.log("Found RDSK block at block %d (%08x)\n"
                             % (offset, offset * 512), 4)
                    valid = 1
                else:
                    self.log("Found RDSK at block %d (%08x) but with bad "
                             "checksum\n" % (offset, offset * 512), 2)

            if str(rdsk[0:4]) == "DRKS":
                self.log("Found byte flipped RDSK block at block "
                         "%d (%08x)\n" % (offset, offset * 512), 4)
                valid = 1
                self.flip = 1

                # If byte order is flipped, re-read RDSK block
            
                rdsk = self.read_block(offset)

            if valid == 0:
                offset += 1

                if offset > max_block:
                    msg = "File %s is not a valid Amiga RDSK image" \
                        % self.file_name
                    raise rdsk_exception(msg)
            else:
                self.rdsk_raw = rdsk
                return offset

    #
    # Locate any FSHD blocks and return an array with tuples (offset, data)
    #

    def scan_fshd(self, max_block = 16):

        ret = []

        for offset in range(self.rdsk_pos, self.rdsk_pos + max_block):
            data = self.read_block(offset)
            if(str(data[0:4]) == "FSHD"):
                if(rdsk_checksum(data)):
                    fshd = fshd_block(data, self)
                    ret.append(( offset, fshd ))
                    
            offset += 1

        return ret

    #
    # Create readable te
    #

    def info(self):

        r = self.rdsk
        sm = self.total_size / (1024 * 1024)
        if self.flip:
            o = "Flipped"
        else:
            o = "Normal"

        ret = \
            "Raw file size  %d bytes (%08x)\n" \
            "RDSK size      %d bytes (%08x, %dM)\n" \
            "RDSK offset    %d blocks (ofs %08x)\n" \
            "Byte order     %s\n" \
            "Block size     %d\n" \
            "Cylinders      %d\n" \
            "Sectors        %d\n" \
            "Heads          %d\n" \
            "Blks per cyl   %d\n" \
            "Flags          0x%02x\n" \
            "PART list      %08x\n" \
            "FS header      %d (%08x)\n" \
            "Drive init     %d (%08x)\n" \
            "RDB blk lo     %d (%08x)\n" \
            "RDB blk hi     %d (%08x)\n" \
            "LoCyl          %d\n" \
            "HiCyl          %d\n" \
            "Vendor         %s\n" \
            "Product        %s\n" \
            "Revision       %s\n" \
            % (self.raw_size, self.raw_size, # Image file raw size
               self.total_size, self.total_size, sm, # Size
               self.rdsk_pos, self.rdsk_pos * self.blocksize,
               o, # Byte order
               self.blocksize,
               self.cylinders, # Cylinders
               self.sectors, # Sectors
               self.heads, # Heads
               self.cylblks, # Blks per cyl
               r[5], # Flags
               r[7], # PART list
               self.fshdrlist, int(self.fshdrlist * self.blocksize),
               self.driveinit, int(self.driveinit * self.blocksize),
               self.rdblo, self.rdblo * self.blocksize,
               self.rdbhi, self.rdbhi * self.blocksize,
               self.locyl, # Lo cyl
               self.hicyl, # Hi cyl
               r[40], # Vendor
               r[41], # Prod
               r[42] # Rev
               )

        for p in self.part:
            ret += "\n" + p.part_info()

        
        return ret


    def read_block(self, blockno, chksum = False):

        if debug:
            print "Reading block %d" % blockno

        self.file.seek(blockno * 512)
        data = self.file.read(512)

        # Flip byte order (takes a long time!)

        if self.flip:
            data_copy = ""
            pos = 0
            while pos < 512:
                data_copy += data[pos + 1]
                data_copy += data[pos]
                pos += 2
            data = data_copy

        # Do checksum

        sumok = True
        if chksum:
            if not rdsk_checksum(data):
                sumok = False

        if debug or not sumok:
            #dump(data)
            pass

        if not sumok:
            raise rdsk_checksum_exception(blockno)

        return data


    def log(self, msg, lvl = 3):

        if self.dbglvl >= lvl:
            print msg,


    def save_partition(self, partno, filename): # Is this used?

        p = self.part[partno]
        p.save_as_file(filename)


    # Scan all blocks looking for files
        
    def scan(self, rex):
        for p in self.part:
            p.scan(rex)
            

def do_list(file, regexp, opts, partno):


    r = rdsk_disk(file)
    if partno >= len(r.part):
        print "No such partition (max %d)" % (len(r.part) - 1)
        sys.exit(1)
    p = r.part[partno]

    print "Size       XPK  Ratio Orig size  Hdrblk   Path"
    print "---------- ---- ----- ---------- -------- ------------------------------"

    nodes = p.get_a_list_of_files(regexp)
    for n in nodes:
        if n.is_file():
            ln = "%10d %4s %4d%% %10d %08x %s" \
                % (n.size, n.xpktype, n.xpkratio, n.xpkorigsize, n.blkno, n.full_path)
        else:
            ln = (" " * (10 + 1 + 4 + 1 + 5 + 1 + 10 + 1)) + "%08x %s" \
                % (n.blkno, n.full_path)
        print ln
        if ("-l", "") in opts:
            print " " + n.inf

        if n.is_file():
            n.xpk_analyze()


def do_extract(file, regexp, opts):

    r = rdsk_disk(file)
    p = r.part[0]
    nodes = p.get_a_list_of_files(regexp)

    for n in nodes:
        if n.is_file():
            print "%8d %-60s " % (n.size, n.full_path),
            pl = str(n.full_path).split("/")
            cwd = os.getcwd()
            if len(pl) > 0:
                for d in pl[:-1]:
                    curr = pl[0]
                    del pl[0]
                    if not os.path.isdir(curr):
                        os.mkdir(curr)
                    os.chdir(curr)
                if not os.path.isfile(n.name):
                    try:
                        data = n.get()
                        f = open(n.name, "w")
                        f.write(data)
                        f.close()
                        print "ok"
                    except rdsk_exception, e:
                        print "error"
                    except rdsk_checksum_exception, e:
                        print "bad chksum blk %08x" % e.blockno
                else:
                    print "exists"
            else:
                print "grr"
                
            os.chdir(cwd)
                    

def do_info(file, opts):

    r = rdsk_disk(file)
    print "RDSK info:"
    print r.info()

    
def do_part(partno, partfile, fn):
    r = rdsk_disk(fn)
    print "Extracting partition %d from image %s to file %s .." % \
        (partno, fn, partfile)
    r.save_partition(partno, partfile)


def do_scan(fn, rex): # TODO scan all blocks looking for files
    r = rdsk_disk(fn)
    print r.info()
    r.scan(rex)
    
def display_usage():

    print \
          "adisk (C) Dan Hovang 2008" \
          "Reads Amiga RDSK hard disk images.\n" \
          "Usage:\n" \
          "adisk <options> [command] [image file]\n" \
          " Command        Arguments           Description\n" \
          "  l, list       regexp          display contents matching regexp\n" \
          "  x, extract    regexp          extract files matching regexp\n" \
          "  i, info                       display information\n" \
          "  p, part       partno  file    extract partition\n" \
          "  s, scan       regexp          scan disk for files\n" \
          "\n" \
          " Options\n" \
          "  -v <level>       Set verbose level 0-5 (0 is default)\n" \
          "  -d <file>        Enable debug output to <file>\n" \
          "  -l               Generate long listing\n" \
          "  -p <partition>   Use specific partition (default is 0)\n",
    
#
# MAIN
#

def main():

    # Check input parameters

    if len(sys.argv) <= 2:
        display_usage()
        sys.exit(0)

    opts, args = getopt.getopt(sys.argv[1:], "d:v:p:l")

    # Parse common options

    partno = 0
    for o in opts:
        if o[0] == "-p":
            partno = int(o[1])

    # Pase commands
    
    c = args[0]
    if c == "list" or c == "l":
        if len(args) > 2:
            fn = args[2]
            rex = args[1]
        else:
            fn = args[1]
            rex = ".*"
        do_list(fn, rex, opts, partno)
    elif c == "extract" or c == "x":
        if len(args) > 2:
            fn = args[2]
            rex = args[1]
        else:
            fn = args[1]
            rex = ".*"
        do_extract(fn, rex, opts)
    elif c == "info" or c == "i":
        do_info(args[1], opts)
    elif c == "part" or c == "p":
        if len(args) == 4:
            fn = args[3]
            partfile = args[2]
            partno = int(args[1])
            do_part(partno, partfile, fn)
        else:
            print "Wrong number of arguments"
            sys.exit(1)
    elif c == "scan" or c == "s":
        if len(args) > 2:
            fn = args[2]
            rex = args[1]
        else:
            fn = args[1]
            rex = ".*"
        do_scan(fn, rex)
    else:
        print "Bad command '%s'" % c
        print "Type adisk for help"
        sys.exit(1)

if __name__ == "__main__":
    try:
        main()
    except rdsk_exception, e:
        print traceback.print_tb(sys.exc_info()[2])
        print e.get_msg()
