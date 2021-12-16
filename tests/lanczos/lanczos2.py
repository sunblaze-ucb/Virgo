#!/usr/bin/python
#
# (C) 2017 Riad S. Wahby <rsw@cs.nyu.edu>
#
# generate a PWS and RDL for a 2-lobe Lanczos ("Lanczos2") downsampling filter

import math
import sys

NBITS=16

# given the downsample size, compute the filter coefficients
def filter_coeffs(ratio):
    #
    # This is based on
    # @incollection{turkowski90filters,
    #    author={Ken Turkowski},
    #    title={Filters for common resampling tasks},
    #    booktitle={Graphics Gems},
    #    xeditor={Andrew S. Glassner},
    #    pages={147--165},
    #    publisher={Academic Press},
    #    year=1990,
    #    xaddress={San Diego, {CA}},
    # }
    #

    spacing = 1.0/ratio
    offset = spacing/2.0

    return [ int(2**(NBITS+4) * math.sin(math.pi * pt) * math.sin(math.pi/2 * pt) / (math.pi**2 / 2 * pt**2) / ratio) << NBITS for pt in [ offset + idx * spacing for idx in range(0, 2 * ratio) ] ]

def print_pws(ratio, fh):
    # PWS has 2*ratio scalar and 16*ratio^2 pixel inputs
    # pixels are given in column-major form
    voffset = 16 * ratio ** 2 + 2 * ratio
    for inidx in range(0, voffset):
        fh.write("P V%d = I%d E\n" % (inidx, inidx))

    coeffs_idx = range(voffset - 2*ratio, voffset)
    coeffs_idx = list(reversed(coeffs_idx)) + list(coeffs_idx)

    def print_lanczos_muls(row, voffset):
        assert len(row) == len(coeffs_idx)

        outs = []
        for (idx, elm) in enumerate(row):
            fh.write("P V%d = V%d * V%d E\n" % (voffset, elm, coeffs_idx[idx]))
            outs.append(voffset)
            voffset += 1
        return (outs, voffset)

    def print_add_tree(ivals, voffset):
        outs = []
        for idx in range(0, len(ivals)//2):
            fh.write("P V%d = V%d + V%d E\n" % (voffset, ivals[2*idx], ivals[2*idx+1]))
            outs.append(voffset)
            voffset += 1

        if len(ivals) % 2 != 0:
            outs.append(ivals[-1])

        if len(outs) == 1:
            return (outs[0], voffset)
        else:
            return print_add_tree(outs, voffset)

    outs = []
    for xidx in range(0, 4 * ratio):
        (ovals, voffset) = print_lanczos_muls([4*ratio*xidx + off for off in range(0, 4*ratio)], voffset)
        (aval, voffset) = print_add_tree(ovals, voffset)
        outs.append(aval)

    assert len(outs) == 4*ratio
    (ovals, voffset) = print_lanczos_muls(outs, voffset)
    (aval, voffset) = print_add_tree(ovals, voffset)

    fh.write("P O%d = V%d E\n" % (voffset, aval))

def print_rdl(ratio, npixels, N_in, fh):
    # how many sub-ACs do we need?
    n_reps = 1 + (npixels - 4*ratio) // ratio
    N_val = n_reps ** 2
    assert N_in == N_val # just to be sure...

    print "n_reps = %d, N = %d" % (n_reps, N_val)

    n_inputs_subAC = 16 * ratio ** 2 + 2 * ratio
    nbits = (n_inputs_subAC-1).bit_length()
    n_padding = 2 ** nbits - n_inputs_subAC
    assert n_padding > 0

    tot_pixels = npixels ** 2

    # print the inputs
    for inidx in range(0, tot_pixels):
        fh.write("P V%d = I%d E\n" % (inidx, inidx))

    coeffs = filter_coeffs(ratio)
    assert len(coeffs) == 2 * ratio
    for cidx in range(0, len(coeffs)):
        fh.write("P V%d = %d E\n" % (cidx + tot_pixels, coeffs[cidx]))

    voffset = tot_pixels + 2*ratio
    for xrep in range(0, n_reps):
        for yrep in range(0, n_reps):
            assert voffset == tot_pixels + 2*ratio + n_inputs_subAC*(yrep + n_reps * xrep)

            for yoff in range(ratio*yrep, ratio*yrep + 4*ratio):
                for xoff in range(ratio*xrep, ratio*xrep + 4*ratio):
                    pixNum = npixels * yoff + xoff
                    fh.write("P V%d = V%d PASS V%d E\n" % (voffset, pixNum, pixNum))
                    voffset += 1

            for coeff_num in range(0, 2 * ratio):
                fh.write("P V%d = V%d PASS V%d E\n" % (voffset, tot_pixels + coeff_num, tot_pixels + coeff_num))
                voffset += 1

    for oval in range(0, n_inputs_subAC * N_val):
        fh.write("P O%d = V%d E\n" % (voffset, oval + tot_pixels + 2*ratio))
        voffset += 1

if __name__ == "__main__":
    # handle arguments
    if len(sys.argv) < 3:
        print "Usage: %s <downsample ratio> <image dimension>" % sys.argv[0]
        print "  <downsample ratio> is the one-dimensional ratio (e.g., 4x means the image is 16x smaller)"
        print "  <image dimension> is the x- or y-dimension, e.g., 1024 means 1024x1024 image"
        print
        print "Image dimension must be at least 4x the downsample ratio and ratio must divide dimension."
        sys.exit(-1)

    rat = int(sys.argv[1])
    npix = int(sys.argv[2])

    if npix < 4 * rat or npix % rat != 0:
        print "ERROR: Image dimension must be at least 4x the downsample ratio and ratio must divide dimension."
        sys.exit(-1)

    with open("lanczos2_%d.pws" % rat, "w") as f:
        print_pws(rat, f)

    N = (1 + (npix - 4*rat) // rat) ** 2
    with open("lanczos2_%d_%d_N=%d_rdl.pws" % (rat, npix, N), "w") as f:
        print_rdl(rat, npix, N, f)
