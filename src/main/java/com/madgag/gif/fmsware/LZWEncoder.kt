package com.madgag.gif.fmsware

import java.io.IOException
import java.io.OutputStream
import kotlin.math.max

/**
 * Adapted from Jef Poskanzer's Java port by way of J. M. G. Elliott.
 * K Weiner 12/00
 *
 * GIFCOMPR.C       - GIF Image compression routines
 *
 * Lempel-Ziv compression based on 'compress'.  GIF modifications by
 * David Rowley (mgardi@watdcsu.waterloo.edu)
 *
 * GIF Image compression - modified 'compress'
 *
 * Based on: compress.c - File compression ala IEEE Computer, June 1984.
 *
 * By Authors:  Spencer W. Thomas      (decvax!harpo!utah-cs!utah-gr!thomas)
 *              Jim McKie              (decvax!mcvax!jim)
 *              Steve Davies           (decvax!vax135!petsd!peora!srd)
 *              Ken Turkowski          (decvax!decwrl!turtlevax!ken)
 *              James A. Woods         (decvax!ihnp4!ames!jaw)
 *              Joe Orost              (decvax!vax135!petsd!joe)
 */
class LZWEncoder(
  private var imgW: Int,
  private var imgH: Int,
  private var pixAry: ByteArray?,
  color_depth: Int
) {

  private var initCodeSize: Int = max(2, color_depth)
  private var remaining: Int = 0
  private var curPixel: Int = 0

  // GIFCOMPR.C       - GIF Image compression routines
  //
  // Lempel-Ziv compression based on 'compress'.  GIF modifications by
  // David Rowley (mgardi@watdcsu.waterloo.edu)

  // GIF Image compression - modified 'compress'
  //
  // Based on: compress.c - File compression ala IEEE Computer, June 1984.
  //
  // By Authors:  Spencer W. Thomas      (decvax!harpo!utah-cs!utah-gr!thomas)
  //              Jim McKie              (decvax!mcvax!jim)
  //              Steve Davies           (decvax!vax135!petsd!peora!srd)
  //              Ken Turkowski          (decvax!decwrl!turtlevax!ken)
  //              James A. Woods         (decvax!ihnp4!ames!jaw)
  //              Joe Orost              (decvax!vax135!petsd!joe)

  private var n_bits: Int = 0 // number of bits/code
  private var maxbits = BITS // user settable max # bits/code
  private var maxcode: Int = 0 // maximum code, given n_bits
  private var maxmaxcode = 1 shl BITS // should NEVER generate this code

  private var htab = IntArray(HSIZE)
  private var codetab = IntArray(HSIZE)

  private var hsize = HSIZE // for dynamic table sizing

  private var free_ent = 0 // first unused entry

  // block compression parameters -- after all codes are used up,
  // and compression rate changes, start over.
  private var clear_flg = false

  // Algorithm:  use open addressing double hashing (no chaining) on the
  // prefix code / next character combination.  We do a variant of Knuth's
  // algorithm D (vol. 3, sec. 6.4) along with G. Knott's relatively-prime
  // secondary probe.  Here, the modular division first probe is gives way
  // to a faster exclusive-or manipulation.  Also do block compression with
  // an adaptive reset, whereby the code table is cleared when the compression
  // ratio decreases, but after the table fills.  The variable-length output
  // codes are re-sized at this point, and a special CLEAR code is generated
  // for the decompressor.  Late addition:  construct the table according to
  // file size for noticeable speed improvement on small files.  Please direct
  // questions about this implementation to ames!jaw.

  private var g_init_bits: Int = 0

  private var ClearCode: Int = 0
  private var EOFCode: Int = 0

  // output
  //
  // Output the given code.
  // Inputs:
  //      code:   A n_bits-bit integer.  If == -1, then EOF.  This assumes
  //              that n_bits =< wordsize - 1.
  // Outputs:
  //      Outputs code to the file.
  // Assumptions:
  //      Chars are 8 bits long.
  // Algorithm:
  //      Maintain a BITS character long buffer (so that 8 codes will
  // fit in it exactly).  Use the VAX insv instruction to insert each
  // code in turn.  When the buffer fills up empty it and start over.

  private var cur_accum = 0
  private var cur_bits = 0

  private var masks = intArrayOf(
      0x0000,
      0x0001,
      0x0003,
      0x0007,
      0x000F,
      0x001F,
      0x003F,
      0x007F,
      0x00FF,
      0x01FF,
      0x03FF,
      0x07FF,
      0x0FFF,
      0x1FFF,
      0x3FFF,
      0x7FFF,
      0xFFFF
  )

  // Number of characters so far in this 'packet'
  private var a_count: Int = 0

  // Define the storage for the packet accumulator
  private var accum = ByteArray(256)

  @Throws(IOException::class)
  fun encode(os: OutputStream) {
    os.write(initCodeSize) // write "initial code size" byte

    remaining = imgW * imgH // reset navigation variables
    curPixel = 0

    compress(initCodeSize + 1, os) // compress and write the pixel data

    os.write(0) // write block terminator
  }

  // table clear for block compress
  private fun cl_block(outs: OutputStream) {
    cl_hash(hsize)
    free_ent = ClearCode + 2
    clear_flg = true

    output(ClearCode, outs)
  }

  // Add a character to the end of the current packet, and if it is 254
  // characters, flush the packet to dis
  private fun char_out(
    c: Byte,
    outs: OutputStream
  ) {
    accum[a_count++] = c
    if (a_count >= 254) flush_char(outs)
  }

  // reset code table
  private fun cl_hash(hsize: Int) {
    for (i in 0 until hsize)
      htab[i] = -1
  }

  // Flush the packet to disk, and reset the accumulator
  private fun flush_char(outs: OutputStream) {
    if (a_count > 0) {
      outs.write(a_count)
      outs.write(accum, 0, a_count)
      a_count = 0
    }
  }

  private fun MAXCODE(n_bits: Int): Int {
    return (1 shl n_bits) - 1
  }

  //----------------------------------------------------------------------------
  // Return the next pixel from the image
  //----------------------------------------------------------------------------
  private fun nextPixel(): Int {
    if (remaining == 0) return EOF

    --remaining

    val pix = pixAry!![curPixel++].toInt()

    return pix and 0xff
  }

  private fun compress(
    init_bits: Int,
    outs: OutputStream?
  ) {
    var fcode: Int
    var i: Int
    var c: Int
    var ent: Int
    var disp: Int
    val hsize_reg: Int = hsize
    var hshift = 0

    // Set up the globals:  g_init_bits - initial number of bits
    g_init_bits = init_bits

    // Set up the necessary values
    clear_flg = false
    n_bits = g_init_bits
    maxcode = MAXCODE(n_bits)

    ClearCode = 1 shl (init_bits - 1)
    EOFCode = ClearCode + 1
    free_ent = ClearCode + 2

    a_count = 0 // clear packet

    ent = nextPixel()

    fcode = hsize
    while (fcode < 65536) {
      ++hshift
      fcode *= 2
    }
    hshift = 8 - hshift // set hash code range bound

    cl_hash(hsize_reg) // clear hash table

    output(ClearCode, outs!!)

    c = nextPixel()
    outer_loop@ while (c != EOF) {
      fcode = (c shl maxbits) + ent
      i = (c shl hshift) xor ent // xor hashing

      if (htab[i] == fcode) {
        ent = codetab[i]
        c = nextPixel()
        continue
      } else if (htab[i] >= 0)
      // non-empty slot
      {
        disp = hsize_reg - i // secondary hash (after G. Knott)
        if (i == 0) disp = 1
        do {
          i -= disp
          if (i < 0) i += hsize_reg

          if (htab[i] == fcode) {
            ent = codetab[i]
            c = nextPixel()
            continue@outer_loop
          }
        } while (htab[i] >= 0)
      }
      output(ent, outs)
      ent = c
      if (free_ent < maxmaxcode) {
        codetab[i] = free_ent++ // code -> hashtable
        htab[i] = fcode
      } else {
        cl_block(outs)
      }

      c = nextPixel()
    }
    // Put out the final code.
    output(ent, outs)
    output(EOFCode, outs)
  }

  private fun output(
    code: Int,
    outs: OutputStream
  ) {
    cur_accum = cur_accum and masks[cur_bits]

    cur_accum = if (cur_bits > 0) cur_accum or (code shl cur_bits) else code

    cur_bits += n_bits

    while (cur_bits >= 8) {
      char_out((cur_accum and 0xff).toByte(), outs)
      cur_accum = cur_accum shr 8
      cur_bits -= 8
    }

    // If the next entry is going to be too big for the code size,
    // then increase it, if possible.
    if (free_ent > maxcode || clear_flg) {
      if (clear_flg) {
        n_bits = g_init_bits
        maxcode = MAXCODE(n_bits)
        clear_flg = false
      } else {
        ++n_bits
        if (n_bits == maxbits) {
          maxcode = maxmaxcode
        } else {
          maxcode = MAXCODE(n_bits)
        }
      }
    }

    if (code == EOFCode) {
      // At EOF, write the rest of the buffer.
      while (cur_bits > 0) {
        char_out((cur_accum and 0xff).toByte(), outs)
        cur_accum = cur_accum shr 8
        cur_bits -= 8
      }

      flush_char(outs)
    }
  }

  companion object {

    internal const val EOF = -1

    internal const val BITS = 12

    /** 80% occupancy */
    internal const val HSIZE = 5003
  }
}
