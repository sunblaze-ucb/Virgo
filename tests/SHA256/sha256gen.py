#!/usr/bin/python

import getopt
import os
import sys
import tempfile

def debug(dstr):
    global VERBOSE
    if VERBOSE:
        print dstr

#out[i]=(x[i]&y[i])^(~x[i]&z[i])
def writeCHfunction(fh, x, y, z, voffset):
    x_and_y = []
    for (xval, yval) in zip(x, y):
        fh.write("P V%d = V%d * V%d E\n" % (voffset, xval, yval))
        x_and_y.append(voffset)
        voffset += 1

    nx_and_z = []
    for (xval, zval) in zip(x, z):
        fh.write("P V%d = V%d NAAB V%d E\n" % (voffset, xval, zval))
        nx_and_z.append(voffset)
        voffset += 1

    outs = []
    for (xay, nxaz) in zip(x_and_y, nx_and_z):
        fh.write("P V%d = V%d XOR V%d E\n" % (voffset, xay, nxaz))
        outs.append(voffset)
        voffset += 1

    return (outs, voffset)

#out[i]=x[i]^y[i]^z[i]
def writeXORSfunction(fh, x, y, z, voffset):
    x_xor_y = []
    for (xval, yval) in zip(x, y):
        fh.write("P V%d = V%d XOR V%d E\n" % (voffset, xval, yval))
        x_xor_y.append(voffset)
        voffset += 1

    outs = []
    for (xxy, zval) in zip(x_xor_y, z):
        fh.write("P V%d = V%d XOR V%d E\n" % (voffset, xxy, zval))
        outs.append(voffset)
        voffset += 1

    return (outs, voffset)

#out[i]=(x[i]&y[i])^(y[i]&z[i])^(x[i]&z[i])
def writeMAJfunction(fh, x, y, z, voffset):
    x_and_y = []
    y_and_z = []
    x_and_z = []
    for (xval, yval, zval) in zip(x, y, z):
        fh.write( "P V%d = V%d * V%d E\n" % (voffset, xval, yval))
        x_and_y.append(voffset)
        voffset += 1

        fh.write( "P V%d = V%d * V%d E\n" % (voffset, yval, zval))
        y_and_z.append(voffset)
        voffset += 1

        fh.write( "P V%d = V%d * V%d E\n" % (voffset, xval, zval))
        x_and_z.append(voffset)
        voffset += 1

    return writeXORSfunction(fh, x_and_y, y_and_z, x_and_z, voffset)

#out=ROTR(x,2)^ROTR(x,13)^ROTR(x,22)
def writeSigma0function(fh, x, voffset):
    ROTR_2 = x[2:] + x[:2]
    ROTR_13 = x[13:] + x[:13]
    ROTR_22 = x[22:] + x[:22]
    return writeXORSfunction(fh, ROTR_2, ROTR_13, ROTR_22, voffset)

#out=ROTR(x,6)^ROTR(x,11)^ROTR(x,25)
def writeSigma1function(fh, x, voffset):
    ROTR_6 = x[6:] + x[:6]
    ROTR_11 = x[11:] + x[:11]
    ROTR_25 = x[25:] + x[:25]
    return writeXORSfunction(fh, ROTR_6, ROTR_11, ROTR_25, voffset)

#out=ROTR(x,7)^ROTR(x,18)^SHR(x,3)
def writesigma0function(fh, x, voffset):
    # V0 is the constant 0

    ROTR_7 = x[7:] + x[:7]
    ROTR_18 = x[18:] + x[:18]
    SHR_3 = x[3:] + [0] * 3
    return writeXORSfunction(fh, ROTR_7, ROTR_18, SHR_3, voffset)

#out=ROTR(x,17)^ROTR(x,19)^SHR(x,10)
def writesigma1function(fh, x, voffset):
    # V0 is the constant 0

    ROTR_17 = x[17:] + x[:17]
    ROTR_19 = x[19:] + x[:19]
    SHR_10 = x[10:] + [0] * 10
    return writeXORSfunction(fh, ROTR_17, ROTR_19, SHR_10, voffset)

# print out an add tree given a list of inputs
def print_add_tree(fh, ivals, voffset, maxlength=1):
    while len(ivals) > maxlength:
        outs = []
        for idx in range(0, len(ivals) // 2):
            fh.write("P V%d = V%d + V%d E\n" % (voffset, ivals[2*idx], ivals[2*idx+1]))
            outs.append(voffset)
            voffset += 1

        if len(ivals) % 2 != 0:
            outs.append(ivals[-1])

        ivals = outs

    if maxlength > 1:
        return (ivals, voffset)
    else:
        return (ivals[0], voffset)

# sum a bit vector into a single field element
def do_addition(fh, ivals, voffset, noconsts):
	for i in range(len(ivals) - 1):
		assert ivals[i] + 1 == ivals[i + 1]
	fh.write("P V%d = V%d EXPSUM V%d E\n" % (voffset, ivals[0], ivals[len(ivals) - 1]))
	voffset += 1
	return (voffset - 1, voffset)
#
#    ovals = [ivals[0]] + list(range(voffset, voffset + len(ivals) - 1))

    # unnecessary optimization: 2x = x + x
#    fh.write("P V%d = V%d + V%d E\n" % (voffset, ivals[1], ivals[1]))
#    voffset += 1

#    if noconsts:
#        expIn = 1
#        for ival in ivals[2:]:
#            fh.write("P V%d = V%d * V%d E\n" % (voffset, expIn, ival))
#            voffset += 1
#            expIn += 1
#    else:
#        exp = 4
#        for ival in ivals[2:]:
#            fh.write("P V%d = %d * V%d E\n" % (voffset, exp, ival))
#            voffset += 1
#            exp *= 2

#    return print_add_tree(fh, ovals, voffset)

def test_field_field(fh, fval1, fval2, condition, voffset):
    fh.write("P V%d = V%d minus V%d E\n" % (voffset, fval1, fval2))
    voffset += 1

    if condition is not None:
        fh.write("P V%d = V%d * V%d E\n" % (voffset, voffset-1, condition))
        voffset += 1

    return (voffset - 1, voffset)

def test_bitvec_field(fh, bvals, fval, condition, voffset, noconsts):
    (bsum, voffset) = do_addition(fh, bvals, voffset, noconsts)
    return test_field_field(fh, bsum, fval, condition, voffset)

def verify_bits(fh, ivals, voffset):
    outs = []
    for ival in ivals:
        #fh.write("P V%d = V%d NOT V%d E\n" % (voffset, ival, ival))
        #fh.write("P V%d = V%d * V%d E\n" % (voffset+1, voffset, ival))
        fh.write("P V%d = V%d BIT V%d E\n" % (voffset, ival, ival))
        outs.append(voffset)
        voffset += 1

    return (outs, voffset)

def allocate_input(voffset, inVals, extent=None):
    if extent is None:
        inVals.append(voffset)
        return (voffset, voffset + 1)
    else:
        outVals = list(range(voffset, voffset + extent))
        inVals.extend(outVals)
        return (outVals, voffset + extent)

def write_4_rounds(fh, finfh, randzero, noconsts):
    # start with V34 because V0--V33 are constants 0, 4, 8, 16, 32, ...
    v_initial = 34
    voffset = v_initial

    ########################### step 1: define all inputs
    #####################################################
    inVals = []
    alloc = lambda voffset, extent=None: allocate_input(voffset, inVals, extent)

    W_i = {}
    W_i_bits = {}
    H_i = []
    K_i = []
    Hout_i = []
    Hout_i_bits = []

    # 1 if this is the first round (meaning we have to check that a-h equal H0-H7)
    (in_first_round, voffset) = alloc(voffset)

    # 1 if this is round > 15
    (not_early_round, voffset) = alloc(voffset)

    # 1 if this is rounds 60-63
    (in_final_round, voffset) = alloc(voffset)

    # guiding principle: any values generated here get checked; otherwise, they're
    #                    coming from another sub-AC where they were checked.

    win_offset_length = [(16, 4, None), (7, 4, None), (0, 4, None), (15, 4, 32), (2, 2, 32), (0, 4, 34)]
    # tuple[2]:
    # "None" means "finite field elem repr"
    # a number means bitwise repr with that many bits
    # need 34 bits of Wi0-3 because we are going to use these to check mod-2^32 sums
    for (offset, length, bitlength) in win_offset_length:
        if bitlength is None:
            for i in range(0, length):
                debug("W_(%d) is input %d" % (i - offset, voffset))
                (W_i[i - offset], voffset) = alloc(voffset)
        else:
            for i in range(0, length):
                debug("W_(%d)[%d] starts at input %d" % (i - offset, bitlength, voffset))
                (W_i_bits[i - offset], voffset) = alloc(voffset, bitlength)

    # K0 through K3
    for i in range(0, 4):
        debug("K_(%d) is input %d" % (i, voffset))
        (tmp, voffset) = alloc(voffset)
        K_i.append(tmp)

    # starting H0 through H7
    for i in range(0, 8):
        debug("Hin_(%d) is input %d" % (i, voffset))
        (tmp, voffset) = alloc(voffset)
        H_i.append(tmp)

    # final H0 through H7 --- only used when hashing many blocks
    for i in range(0, 8):
        debug("Hout_(%d) is input %d" % (i, voffset))
        (tmp, voffset) = alloc(voffset)
        Hout_i.append(tmp)

    # final H0 through H7, in bits
    bitlength = 33
    for i in range(0, 8):
        debug("Hout_(%d)[%d] starts at input %d" % (i, bitlength, voffset))
        (tmp, voffset) = alloc(voffset, bitlength)
        Hout_i_bits.append(tmp)

    # a, b, c, d, e, f, g, h
    # we need d and h as field elements, the rest as bits
    debug("d_field is input %d" % (voffset))
    (d_field, voffset) = alloc(voffset)

    debug("h_field is input %d" % (voffset))
    (h_field, voffset) = alloc(voffset)

    debug("a_bits[32] starts at input %d" % (voffset))
    (a_bits, voffset) = alloc(voffset, 32)

    debug("b_bits[32] starts at input %d" % (voffset))
    (b_bits, voffset) = alloc(voffset, 32)

    debug("c_bits[32] starts at input %d" % (voffset))
    (c_bits, voffset) = alloc(voffset, 32)

    debug("e_bits[32] starts at input %d" % (voffset))
    (e_bits, voffset) = alloc(voffset, 32)

    debug("f_bits[32] starts at input %d" % (voffset))
    (f_bits, voffset) = alloc(voffset, 32)

    debug("g_bits[32] starts at input %d" % (voffset))
    (g_bits, voffset) = alloc(voffset, 32)

    # outputs, including field elements for d and h (those go to the next sub-AC)
    debug("d_out is input %d" % (voffset))
    (d_out, voffset) = alloc(voffset)

    debug("h_out is input %d" % (voffset))
    (h_out, voffset) = alloc(voffset)
    aout_bits = []
    eout_bits = []
    bitlength = 35
    for (target, name) in ((aout_bits, "a"), (eout_bits, "e")):
        for i in range(0, 4):
            debug("%s_out(%d)[%d] starts at input %d" % (name, i, bitlength, voffset))
            (tmp, voffset) = alloc(voffset, 35)
            target.append(tmp)

    ####################### step 2: sums and input checks
    #####################################################
    bit_tests = []
    round_tests = []

    (a_field, voffset) = do_addition(fh, a_bits, voffset, noconsts)
    (b_field, voffset) = do_addition(fh, b_bits, voffset, noconsts)
    (c_field, voffset) = do_addition(fh, c_bits, voffset, noconsts)
    (e_field, voffset) = do_addition(fh, e_bits, voffset, noconsts)
    (f_field, voffset) = do_addition(fh, f_bits, voffset, noconsts)
    (g_field, voffset) = do_addition(fh, g_bits, voffset, noconsts)

    # test all inputs that are purportedly bits
    for idx in W_i_bits:
        (tmp, voffset) = verify_bits(fh, W_i_bits[idx], voffset)
        bit_tests.extend(tmp)

    for vecs in (Hout_i_bits, (a_bits, b_bits, c_bits, e_bits, f_bits, g_bits), aout_bits, eout_bits):
        for vec in vecs:
            (tmp, voffset) = verify_bits(fh, vec, voffset)
            bit_tests.extend(tmp)

    # make sure that d_out and h_out match the values they should
    (tmp, voffset) = test_bitvec_field(fh, aout_bits[0][:32], d_out, None, voffset, noconsts)
    round_tests.append(tmp)
    (tmp, voffset) = test_bitvec_field(fh, eout_bits[0][:32], h_out, None, voffset, noconsts)
    round_tests.append(tmp)

    # in the first round, make sure that the values for a-h match H0-H7
    # (we do this so that V only has to supply field elements corresponding to H0-H7)
    for (val1, val2) in zip([a_field, b_field, c_field, d_field, e_field, f_field, g_field, h_field], H_i):
        (tmp, voffset) = test_field_field(fh, val1, val2, in_first_round, voffset)
        round_tests.append(tmp)

    # in the final round, make sure the given field element equals sum of bottom 32 bits
    for (hbits, hval) in zip(Hout_i_bits, Hout_i):
        (tmp, voffset) = test_bitvec_field(fh, hbits[:32], hval, in_final_round, voffset, noconsts)
        round_tests.append(tmp)

    # make sure that W_i and W_i_bits that will be generated in this ckt match
    # (all W_i_bits need to be tested except W_0 because of sigma_0_wim15)
    for i in range(0, 4):
        condition = None
        if i == 0:
            fh.write("P V%d = V%d NOT V%d E\n" % (voffset, in_first_round, in_first_round))
            condition = voffset
            voffset += 1
        (tmp, voffset) = test_bitvec_field(fh, W_i_bits[i][:32], W_i[i], condition, voffset, noconsts)
        round_tests.append(tmp)

    # check the generated Wi bits
    for rnd in range(0, 4):
        # Wi = sigma1(Wi-2) + Wi-7 + sigma0(Wi-15) + Wi-16
        (sigma_0_wim15_bits, voffset) = writesigma0function(fh, W_i_bits[rnd - 15][:32], voffset)
        (sigma_1_wim2_bits, voffset) = writesigma1function(fh, W_i_bits[rnd - 2][:32], voffset)
        (sigma_0_wim15, voffset) = do_addition(fh, sigma_0_wim15_bits, voffset, noconsts)
        (sigma_1_wim2, voffset) = do_addition(fh, sigma_1_wim2_bits, voffset, noconsts)
        fh.write("P V%d = V%d + V%d E\n" % (voffset, sigma_0_wim15, sigma_1_wim2))
        fh.write("P V%d = V%d + V%d E\n" % (voffset + 1, W_i[rnd - 16], W_i[rnd - 7]))
        fh.write("P V%d = V%d + V%d E\n" % (voffset + 2, voffset + 1, voffset))
        wival = voffset + 2
        voffset += 3

        # test that the purported W_i bitvec is correct
        (tmp, voffset) = test_bitvec_field(fh, W_i_bits[rnd], wival, not_early_round, voffset, noconsts)
        round_tests.append(tmp)

    ################################## step 3: run rounds
    #####################################################
    for rnd in range(0, 4):
        # compute all the bitwise functions
        (Sigma_0_a_bits, voffset) = writeSigma0function(fh, a_bits[:32], voffset)
        (Sigma_1_e_bits, voffset) = writeSigma1function(fh, e_bits[:32], voffset)
        (Maj_abc_bits, voffset) = writeMAJfunction(fh, a_bits[:32], b_bits[:32], c_bits[:32], voffset)
        (Ch_efg_bits, voffset) = writeCHfunction(fh, e_bits[:32], f_bits[:32], g_bits[:32], voffset)
        (Sigma_0_a, voffset) = do_addition(fh, Sigma_0_a_bits, voffset, noconsts)
        (Sigma_1_e, voffset) = do_addition(fh, Sigma_1_e_bits, voffset, noconsts)
        (Maj_abc, voffset) = do_addition(fh, Maj_abc_bits, voffset, noconsts)
        (Ch_efg, voffset) = do_addition(fh, Ch_efg_bits, voffset, noconsts)

        # T2 = Sigma0(a) + Maj(a, b, c)
        fh.write("P V%d = V%d + V%d E\n" % (voffset, Sigma_0_a, Maj_abc))
        t2_val = voffset
        voffset += 1

        # T1 = Sigma1(e) + Ch(e, f, g) + h + Ki + Wi
        fh.write("P V%d = V%d + V%d E\n" % (voffset, Sigma_1_e, Ch_efg))
        t1_late = voffset
        voffset += 1

        fh.write("P V%d = V%d + V%d E\n" % (voffset, K_i[rnd], W_i[rnd]))
        fh.write("P V%d = V%d + V%d E\n" % (voffset + 1, d_field, h_field))
        fh.write("P V%d = V%d + V%d E\n" % (voffset + 2, voffset, voffset + 1))
        fh.write("P V%d = V%d + V%d E\n" % (voffset + 3, voffset + 2, t1_late))
        kiwi = voffset
        enext_field = voffset + 3
        voffset += 4

        fh.write("P V%d = V%d + V%d E\n" % (voffset, t2_val, h_field))
        fh.write("P V%d = V%d + V%d E\n" % (voffset + 1, voffset, kiwi))
        fh.write("P V%d = V%d + V%d E\n" % (voffset + 2, voffset + 1, t1_late))
        anext_field = voffset + 2
        voffset += 3

        # now make sure the input bits equal the values
        (a_test_out, voffset) = test_bitvec_field(fh, aout_bits[rnd], anext_field, None, voffset, noconsts)
        round_tests.append(a_test_out)

        (e_test_out, voffset) = test_bitvec_field(fh, eout_bits[rnd], enext_field, None, voffset, noconsts)
        round_tests.append(e_test_out)

        # finally, update the round values
        h_bits = g_bits
        g_bits = f_bits
        f_bits = e_bits
        e_bits = eout_bits[rnd]
        d_bits = c_bits
        c_bits = b_bits
        b_bits = a_bits
        a_bits = aout_bits[rnd]

        h_field = g_field
        g_field = f_field
        f_field = e_field
        (e_field, voffset) = do_addition(fh, eout_bits[rnd][:32], voffset, noconsts)
        d_field = c_field
        c_field = b_field
        b_field = a_field
        (a_field, voffset) = do_addition(fh, aout_bits[rnd][:32], voffset, noconsts)

    ########################## step 4: verify H_i outputs
    #####################################################
    final_field_vals = [a_field, b_field, c_field, d_field, e_field, f_field, g_field, h_field]
    for (rdval, hinval, houtbits) in zip(final_field_vals, H_i, Hout_i_bits):
        fh.write("P V%d = V%d + V%d E\n" % (voffset, rdval, hinval))
        houtval = voffset
        voffset += 1

        (tmp, voffset) = test_bitvec_field(fh, houtbits, houtval, in_final_round, voffset, noconsts)
        round_tests.append(tmp)

    ####################### step 5: do randomized 0 tests
    #####################################################
    if randzero:
        # bit_tests, round_tests
        rvals_start = len(inVals)
        def rand_muls(testvec, voffset):
            testouts = []
            for elm in testvec:
                fh.write("P V%d = V%d * V%d E\n" % (voffset + 1, voffset, elm))
                testouts.append(voffset + 1)
                inVals.append(voffset)
                voffset += 2

            return print_add_tree(fh, testouts, voffset)

        (tmp, voffset) = rand_muls(bit_tests, voffset)
        round_tests.append(tmp)
        debug("rvalues start at input %d, total %d" % (rvals_start + v_initial, len(inVals) - rvals_start))
    else:
        round_tests.extend(bit_tests)

    ############################# step 6: write final PWS
    #####################################################
    # write constants first
    if noconsts:
        for ionum in xrange(v_initial):
            finfh.write("P V%d = I%d E\n" % (ionum, ionum))
    else:
        finfh.write("P V0 = 0 E\n")
        exp = 4
        for i in range(1, v_initial):
            finfh.write("P V%d = %d E\n" % (i, exp))
            exp *= 2

    ionum = v_initial
    for inVal in inVals:
        finfh.write("P V%d = I%d E\n" % (inVal, ionum))
        ionum += 1

    fh.seek(0)
    for line in fh:
        finfh.write(line)

    for outVal in round_tests:
        finfh.write("P O%d = V%d E\n" % (voffset, outVal))
        voffset += 1

def write_64_rounds(fh, finfh, randzero, noconsts):
    # start with V34 because V0--V33 are constants 0, 4, 8, 16, 32, ...
    v_initial = 34
    voffset = v_initial

    ########################### step 1: define all inputs
    #####################################################
    inVals = []
    alloc = lambda voffset, extent=None: allocate_input(voffset, inVals, extent)

    W_i = {}
    W_i_bits = {}
    H_i = []
    K_i = []
    Hout_i = []
    Hout_i_bits = []

    win_offset_length = [(0, 64, None), (-1, 15, 32), (-16, 48, 34)]
    # tuple[2]:
    # "None" means "finite field elem repr"
    # a number means bitwise repr with that many bits
    # need 34 bits of Wi0-3 because we are going to use these to check mod-2^32 sums
    for (offset, length, bitlength) in win_offset_length:
        if bitlength is None:
            for i in range(0, length):
                debug("W_(%d) is input %d" % (i - offset, voffset))
                (W_i[i - offset], voffset) = alloc(voffset)
        else:
            for i in range(0, length):
                debug("W_(%d)[%d] starts at input %d" % (i - offset, bitlength, voffset))
                (W_i_bits[i - offset], voffset) = alloc(voffset, bitlength)

    # K0 through K63
    for i in range(0, 64):
        debug("K_(%d) is input %d" % (i, voffset))
        (tmp, voffset) = alloc(voffset)
        K_i.append(tmp)

    # starting H0 through H7
    for i in range(0, 8):
        debug("Hin_(%d) is input %d" % (i, voffset))
        (tmp, voffset) = alloc(voffset)
        H_i.append(tmp)

    # final H0 through H7 --- only used when hashing many blocks
    for i in range(0, 8):
        debug("Hout_(%d) is input %d" % (i, voffset))
        (tmp, voffset) = alloc(voffset)
        Hout_i.append(tmp)

    # final H0 through H7, in bits
    bitlength = 33
    for i in range(0, 8):
        debug("Hout_(%d)[%d] starts at input %d" % (i, bitlength, voffset))
        (tmp, voffset) = alloc(voffset, bitlength)
        Hout_i_bits.append(tmp)

    # a, b, c, e, f, g
    # d and h come in from H_i
    debug("a_bits[32] starts at input %d" % (voffset))
    (a_bits, voffset) = alloc(voffset, 32)

    debug("b_bits[32] starts at input %d" % (voffset))
    (b_bits, voffset) = alloc(voffset, 32)

    debug("c_bits[32] starts at input %d" % (voffset))
    (c_bits, voffset) = alloc(voffset, 32)

    debug("e_bits[32] starts at input %d" % (voffset))
    (e_bits, voffset) = alloc(voffset, 32)

    debug("f_bits[32] starts at input %d" % (voffset))
    (f_bits, voffset) = alloc(voffset, 32)

    debug("g_bits[32] starts at input %d" % (voffset))
    (g_bits, voffset) = alloc(voffset, 32)

    aout_bits = []
    eout_bits = []
    bitlength = 35
    for (target, name) in ((aout_bits, "a"), (eout_bits, "e")):
        for i in range(0, 64):
            debug("%s_out(%d)[%d] starts at input %d" % (name, i, bitlength, voffset))
            (tmp, voffset) = alloc(voffset, 35)
            target.append(tmp)

    ####################### step 2: sums and input checks
    #####################################################
    bit_tests = []
    round_tests = []

    d_field = H_i[3]
    h_field = H_i[7]
    (a_field, voffset) = do_addition(fh, a_bits, voffset, noconsts)
    (b_field, voffset) = do_addition(fh, b_bits, voffset, noconsts)
    (c_field, voffset) = do_addition(fh, c_bits, voffset, noconsts)
    (e_field, voffset) = do_addition(fh, e_bits, voffset, noconsts)
    (f_field, voffset) = do_addition(fh, f_bits, voffset, noconsts)
    (g_field, voffset) = do_addition(fh, g_bits, voffset, noconsts)

    # test inputs that are purportedly bits
    for idx in W_i_bits:
        (tmp, voffset) = verify_bits(fh, W_i_bits[idx], voffset)
        bit_tests.extend(tmp)
        if idx in W_i:
            # check that supplied W_i corresponds to W_i_bits
            # this should make the ckt shallower than requiring W_i to be recreated from W_i_bits
            (tmp, voffset) = test_bitvec_field(fh, W_i_bits[idx][:32], W_i[idx], None, voffset, noconsts)
            round_tests.append(tmp)

    for vecs in (Hout_i_bits, (a_bits, b_bits, c_bits, e_bits, f_bits, g_bits), aout_bits, eout_bits):
        for vec in vecs:
            (tmp, voffset) = verify_bits(fh, vec, voffset)
            bit_tests.extend(tmp)

    # make sure that the values for a-h match H0-H7
    # (we do this so that V only has to supply field elements corresponding to H0-H7)
    for (val1, val2) in zip([a_field, b_field, c_field, e_field, f_field, g_field], H_i[0:3] + H_i[4:7]):
        (tmp, voffset) = test_field_field(fh, val1, val2, None, voffset)
        round_tests.append(tmp)

    # make sure the output H values match the bottom bits of the sum bit expansion
    for (hbits, hval) in zip(Hout_i_bits, Hout_i):
        (tmp, voffset) = test_bitvec_field(fh, hbits[:32], hval, None, voffset, noconsts)
        round_tests.append(tmp)

    # check the Wi bits
    for rnd in range(16, 64):
        # Wi = sigma1(Wi-2) + Wi-7 + sigma0(Wi-15) + Wi-16
        (sigma_0_wim15_bits, voffset) = writesigma0function(fh, W_i_bits[rnd - 15][:32], voffset)
        (sigma_1_wim2_bits, voffset) = writesigma1function(fh, W_i_bits[rnd - 2][:32], voffset)
        (sigma_0_wim15, voffset) = do_addition(fh, sigma_0_wim15_bits, voffset, noconsts)
        (sigma_1_wim2, voffset) = do_addition(fh, sigma_1_wim2_bits, voffset, noconsts)
        fh.write("P V%d = V%d + V%d E\n" % (voffset, sigma_0_wim15, sigma_1_wim2))
        fh.write("P V%d = V%d + V%d E\n" % (voffset + 1, W_i[rnd - 16], W_i[rnd - 7]))
        fh.write("P V%d = V%d + V%d E\n" % (voffset + 2, voffset + 1, voffset))
        wival = voffset + 2
        voffset += 3

        # test that the purported W_i bitvec is correct
        (tmp, voffset) = test_bitvec_field(fh, W_i_bits[rnd], wival, None, voffset, noconsts)
        round_tests.append(tmp)

    ################################## step 3: run rounds
    #####################################################
    for rnd in range(0, 64):
        # compute all the bitwise functions
        (Sigma_0_a_bits, voffset) = writeSigma0function(fh, a_bits[:32], voffset)
        (Sigma_1_e_bits, voffset) = writeSigma1function(fh, e_bits[:32], voffset)
        (Maj_abc_bits, voffset) = writeMAJfunction(fh, a_bits[:32], b_bits[:32], c_bits[:32], voffset)
        (Ch_efg_bits, voffset) = writeCHfunction(fh, e_bits[:32], f_bits[:32], g_bits[:32], voffset)
        (Sigma_0_a, voffset) = do_addition(fh, Sigma_0_a_bits, voffset, noconsts)
        (Sigma_1_e, voffset) = do_addition(fh, Sigma_1_e_bits, voffset, noconsts)
        (Maj_abc, voffset) = do_addition(fh, Maj_abc_bits, voffset, noconsts)
        (Ch_efg, voffset) = do_addition(fh, Ch_efg_bits, voffset, noconsts)

        # T2 = Sigma0(a) + Maj(a, b, c)
        fh.write("P V%d = V%d + V%d E\n" % (voffset, Sigma_0_a, Maj_abc))
        t2_val = voffset
        voffset += 1

        # T1 = Sigma1(e) + Ch(e, f, g) + h + Ki + Wi
        fh.write("P V%d = V%d + V%d E\n" % (voffset, Sigma_1_e, Ch_efg))
        t1_late = voffset
        voffset += 1

        fh.write("P V%d = V%d + V%d E\n" % (voffset, K_i[rnd], W_i[rnd]))
        fh.write("P V%d = V%d + V%d E\n" % (voffset + 1, d_field, h_field))
        fh.write("P V%d = V%d + V%d E\n" % (voffset + 2, voffset, voffset + 1))
        fh.write("P V%d = V%d + V%d E\n" % (voffset + 3, voffset + 2, t1_late))
        kiwi = voffset
        enext_field = voffset + 3
        voffset += 4

        fh.write("P V%d = V%d + V%d E\n" % (voffset, t2_val, h_field))
        fh.write("P V%d = V%d + V%d E\n" % (voffset + 1, voffset, kiwi))
        fh.write("P V%d = V%d + V%d E\n" % (voffset + 2, voffset + 1, t1_late))
        anext_field = voffset + 2
        voffset += 3

        # now make sure the input bits equal the values
        (a_test_out, voffset) = test_bitvec_field(fh, aout_bits[rnd], anext_field, None, voffset, noconsts)
        round_tests.append(a_test_out)

        (e_test_out, voffset) = test_bitvec_field(fh, eout_bits[rnd], enext_field, None, voffset, noconsts)
        round_tests.append(e_test_out)

        # finally, update the round values
        h_bits = g_bits
        g_bits = f_bits
        f_bits = e_bits
        e_bits = eout_bits[rnd]
        d_bits = c_bits
        c_bits = b_bits
        b_bits = a_bits
        a_bits = aout_bits[rnd]

        h_field = g_field
        g_field = f_field
        f_field = e_field
        (e_field, voffset) = do_addition(fh, eout_bits[rnd][:32], voffset, noconsts)
        d_field = c_field
        c_field = b_field
        b_field = a_field
        (a_field, voffset) = do_addition(fh, aout_bits[rnd][:32], voffset, noconsts)

    ########################## step 4: verify H_i outputs
    #####################################################
    final_field_vals = [a_field, b_field, c_field, d_field, e_field, f_field, g_field, h_field]
    for (rdval, hinval, houtbits) in zip(final_field_vals, H_i, Hout_i_bits):
        fh.write("P V%d = V%d + V%d E\n" % (voffset, rdval, hinval))
        houtval = voffset
        voffset += 1

        (tmp, voffset) = test_bitvec_field(fh, houtbits, houtval, None, voffset, noconsts)
        round_tests.append(tmp)

    ####################### step 5: do randomized 0 tests
    #####################################################
    # bit_tests, round_tests
    if randzero:
        rvals_start = len(inVals)
        def rand_muls(testvec, voffset):
            testouts = []
            for elm in testvec:
                fh.write("P V%d = V%d * V%d E\n" % (voffset + 1, voffset, elm))
                testouts.append(voffset + 1)
                inVals.append(voffset)
                voffset += 2

            return print_add_tree(fh, testouts, voffset, 4)

        (tmp, voffset) = rand_muls(bit_tests, voffset)
        round_tests.extend(tmp)
        debug("rvalues start at input %d, total %d" % (rvals_start + v_initial, len(inVals) - rvals_start))
    else:
        round_tests.extend(bit_tests)

    ############################# step 6: write final PWS
    #####################################################
    # write constants first
    if noconsts:
        for ionum in xrange(v_initial):
            finfh.write("P V%d = I%d E\n" % (ionum, ionum))
    else:
        finfh.write("P V0 = 0 E\n")
        exp = 4
        for i in range(1, v_initial):
            finfh.write("P V%d = %d E\n" % (i, exp))
            exp *= 2

    ionum = v_initial
    for inVal in inVals:
        finfh.write("P V%d = I%d E\n" % (inVal, ionum))
        ionum += 1

    fh.seek(0)
    for line in fh:
        finfh.write(line)

    for outVal in round_tests:
        finfh.write("P O%d = V%d E\n" % (voffset, outVal))
        voffset += 1

def write_4_rounds_rdl(fh, randzero):
    debug("\nWriting RDL for 4-round SHA invocation")

    # start with V35 because V0--V34 are constants 0, 1, 4, 8, 16, 32, ...
    v_initial = 35
    voffset = v_initial

    inVals = []
    alloc = lambda voffset, extent=None: allocate_input(voffset, inVals, extent)

    # W_i_bits inputs for 1..63 (not 0, never needed)
    W_i_bits = []
    W_i_bits.append(None)
    for i in range(1, 64):
        if i < 16:
            bitlength = 32
            padding = [0, 0]
        else:
            bitlength = 34
            padding = []
        debug("W_(%d)[%d] starts at input %d" % (i, bitlength, voffset))
        (tmp, voffset) = alloc(voffset, bitlength)
        W_i_bits.append(tmp + padding)

    # W_i inputs for 0..63
    W_i = []
    for i in range(0, 64):
        debug("W_(%d) is input %d" % (i, voffset))
        (tmp, voffset) = alloc(voffset)
        W_i.append(tmp)

    # K_i inputs for 0..63
    K_i = []
    for i in range(0, 64):
        debug("K_(%d) is input %d" % (i, voffset))
        (tmp, voffset) = alloc(voffset)
        K_i.append(tmp)

    # H_i inputs for 0..7
    H_i = []
    for i in range(0, 8):
        debug("H_(%d) is input %d" % (i, voffset))
        (tmp, voffset) = alloc(voffset)
        H_i.append(tmp)

    # Hout_i inputs for 0..7
    Hout_i = []
    for i in range(0, 8):
        debug("Hout_(%d) is input %d" % (i, voffset))
        (tmp, voffset) = alloc(voffset)
        Hout_i.append(tmp)

    # Hout_i_bits inputs for 0..7
    Hout_i_bits = []
    bitlength = 33
    for i in range(0, 8):
        debug("Hout_(%d)_bits[%d] starts at input %d" % (i, bitlength, voffset))
        (tmp, voffset) = alloc(voffset, bitlength)
        Hout_i_bits.append(tmp)

    d_field = []
    for i in range(0, 17):
        debug("d_field(%d) is input %d" % (i, voffset))
        (tmp, voffset) = alloc(voffset)
        d_field.append(tmp)

    h_field = []
    for i in range(0, 17):
        debug("h_field(%d) is input %d" % (i, voffset))
        (tmp, voffset) = alloc(voffset)
        h_field.append(tmp)

    init_bits = []
    bitlength = 32
    for i in range(0, 6):
        debug("init_bits(%d)[%d] starts at input %d" % (i, bitlength, voffset))
        (tmp, voffset) = alloc(voffset, bitlength)
        init_bits.append(tmp)

    a_bits = []
    e_bits = []
    bitlength = 35
    for i in range(0, 64):
        debug("a_bits(%d)[%d] starts at input %d" % (i, bitlength, voffset))
        (tmp, voffset) = alloc(voffset, bitlength)
        a_bits.append(tmp)
    for i in range(0, 64):
        debug("e_bits(%d)[%d] starts at input %d" % (i, bitlength, voffset))
        (tmp, voffset) = alloc(voffset, bitlength)
        e_bits.append(tmp)

    if randzero:
        r_values_len = 1064
        debug("r_values[%d] starts at input %d" % (r_values_len, voffset))
        (r_values, voffset) = alloc(voffset, r_values_len)
    else:
        r_values_len = 0
        r_values = []

    # write the constant inputs
    fh.write("P V0 = 0 E\nP V1 = 1 E\n")
    exp = 4
    for i in range(2, v_initial):
        fh.write("P V%d = %d E\n" % (i, exp))
        exp *= 2

    # write the ckt inputs
    ionum = v_initial
    for inVal in inVals:
        fh.write("P V%d = I%d E\n" % (inVal, ionum))
        ionum += 1

    # now create the outputs
    block_outputs = []
    for block in range(0, 16):
        rstart = 4 * block

        outVals = [0]
        block_outputs.append(outVals)

        # constants
        outVals.extend(range(2, v_initial))

        # in_first_round
        if block == 0:
            outVals.append(1)
        else:
            outVals.append(0)

        # not_early_round
        if block < 4:
            outVals.append(0)
        else:
            outVals.append(1)

        # in_final_round
        if block == 15:
            outVals.append(1)
        else:
            outVals.append(0)

        # W_i-16 .. W_i-13, W_i-7 .. W_i-4
        if block < 4:
            outVals.extend([0, 0, 0, 0, 0, 0, 0, 0])
        else:
            outVals.extend(W_i[rstart - 16:rstart - 12])
            outVals.extend(W_i[rstart - 7:rstart - 3])

        # W_i+0 .. W_i+3
        outVals.extend(W_i[rstart:rstart + 4])

        # W_bits_i-15 .. W_bits_i-12, W_bits_i-2 .. W_bits_i-1      (32 bits)
        if block < 4:
            outVals.extend([0] * 6 * 32)
        else:
            for offset in (15, 14, 13, 12, 2, 1):
                outVals.extend(W_i_bits[rstart - offset][:32])

        # W_bits_i+0 .. W_bits_i+3      (34 bits)
        for i in range(rstart, rstart + 4):
            if i == 0:
                outVals.extend([0] * 34)
            else:
                outVals.extend(W_i_bits[i])

        # Ki+0 .. Ki+3
        for i in range(rstart, rstart + 4):
            outVals.append(K_i[i])

        # H0 .. H7
        for i in range(0, 8):
            outVals.append(H_i[i])

        # Hout0 .. Hout7
        for i in range(0, 8):
            outVals.append(Hout_i[i])

        # Hout_bits0 .. Hout_bits7
        for i in range(0, 8):
            outVals.extend(Hout_i_bits[i])

        # d_field and h_field
        outVals.append(d_field[block])
        outVals.append(h_field[block])

        # a_bits, b_bits, c_bits, e_bits, f_bits, g_bits            (32 bits)
        if block == 0:
            for init in init_bits:
                outVals.extend(init)
        else:
            (c_tmp, b_tmp, a_tmp) = a_bits[4*(block-1)+1:4*block]
            (g_tmp, f_tmp, e_tmp) = e_bits[4*(block-1)+1:4*block]
            for init in (a_tmp, b_tmp, c_tmp, e_tmp, f_tmp, g_tmp):
                outVals.extend(init[:32])

        # d_out and h_out
        outVals.append(d_field[block+1])
        outVals.append(h_field[block+1])

        # aout_bits, eout_bits
        for targ in (a_bits, e_bits):
            for val in targ[4*block:4*block+4]:
                outVals.extend(val)

        # r_values
        outVals.extend(r_values)

    passVals = []
    # generate pass gates
    in_expect_len = 1137
    tot_expect_len = 1137 + r_values_len
    for bout in block_outputs:
        assert len(bout) == tot_expect_len, "bout was wrong len, expected %d got %d" % (tot_expect_len, len(bout))
        for outVal in bout:
            fh.write("P V%d = V%d PASS V%d E\n" % (voffset, outVal, outVal))
            passVals.append(voffset)
            voffset += 1

    # write outvals to file
    for outVal in passVals:
        fh.write("P O%d = V%d E\n" % (ionum, outVal))
        ionum += 1

def write_merkle_rdl(fh, lgnleaves, padding, randzero):
    debug("\nWriting merkle RDL for 2**%d leaves" % lgnleaves)

    # lgnleaves means 2 * 2**lgn - 1
    assert lgnleaves > 0, "Merkle must have at least 2 blocks"
    nblocks = 2 ** (lgnleaves + 1) - 1

    # start with V35 because V0--V34 are constants 0, 4, 8, 16, ...
    v_initial = 34
    voffset = v_initial

    inVals = []
    alloc = lambda voffset, extent=None: allocate_input(voffset, inVals, extent)

    # common inputs for all
    # K_i in 0..63
    K_i = []
    for i in range(0, 64):
        debug("K_(%d) is input %d" % (i, voffset))
        (tmp, voffset) = alloc(voffset)
        K_i.append(tmp)

    # H_i in 0..7
    H_i = []
    for i in range(0, 8):
        debug("H_(%d) is input %d" % (i, voffset))
        (tmp, voffset) = alloc(voffset)
        H_i.append(tmp)

    # init_bits: initial values of a_bits, b_bits, c_bits, e_bits, f_bits, g_bits
    bitlength = 32
    debug("init_{a,b,c,e,f,g}_bits[%d] start at input %d" % (bitlength, voffset))
    (init_bits, voffset) = alloc(voffset, 6 * bitlength)

    # Merkle root
    Hout_final = []
    for i in range(0, 8):
        debug("Hout_final(%d) is input %d" % (i, voffset))
        (tmp, voffset) = alloc(voffset)
        Hout_final.append(tmp)

    # r_values
    if randzero:
        r_values_start = voffset
        r_values_len = 7048
        debug("r_values[%d] starts at input %d" % (r_values_len, voffset))
        (r_values, voffset) = alloc(voffset, r_values_len)
    else:
        r_values_start = -1
        r_values_len = 0
        r_values = []

    # end of public inputs
    pub_idx = len(inVals)
    pub_len = voffset

    # track outputs
    Hout_lay = []
    Hout = [Hout_lay]

    Hout_bits_lay = []
    Hout_bits = [Hout_bits_lay]

    block_inputs = []
    # inputs for each block
    layer = 0
    lay_idx = 0
    for block in range(0, nblocks):
        bkIns = list(range(0, v_initial))
        block_inputs.append(bkIns)
        debug("** block %d:" % block)

        # new layer?
        if lay_idx == 2 ** (lgnleaves - layer):
            layer += 1
            lay_idx = 0
            Hout_lay = []
            Hout.append(Hout_lay)
            Hout_bits_lay = []
            Hout_bits.append(Hout_bits_lay)

        # these are this blocks' output addresses
        Hout_block = []
        Hout_lay.append(Hout_block)
        Hout_bits_block = []
        Hout_bits_lay.append(Hout_bits_block)

        # W_i 0..16
        if layer == 0:
            # these are the leaves of the Merkle tree
            debug("   in_(%d)--in_(%d) start at input %d" % (16*block, 16*block+15, voffset))
            (tmp, voffset) = alloc(voffset, 16)
            bkIns.extend(tmp)
        else:
            # grab from predecessor blocks' outputs
            bkIns.extend(Hout[layer-1][2*lay_idx])
            bkIns.extend(Hout[layer-1][2*lay_idx+1])

        # rest of W_i are always freshly supplied
        debug("   W_16..W63 start at input %d" % voffset)
        (tmp, voffset) = alloc(voffset, 48)
        bkIns.extend(tmp)

        # W_bits_1 .. W_bits_15 are only 32 bits each
        if layer == 0:
            # bit expansions of Merkle leaves
            debug("   in_bits(%d)[32]--in_bits(%d)[32] start at input %d" % (16*block+1, 16*block+15, voffset))
            (tmp, voffset) = alloc(voffset, 15 * 32)
            bkIns.extend(tmp)
        else:
            # grab from predecessor blocks' outputs
            for bits in Hout_bits[layer-1][2*lay_idx][1:] + Hout_bits[layer-1][2*lay_idx+1]:
                bkIns.extend(bits[:32])

        # rest of W_bits_i are always freshly supplied
        debug("   W_bits_16[34]..W_bits_63[34] start at input %d" % voffset)
        (tmp, voffset) = alloc(voffset, 48 * 34)
        bkIns.extend(tmp)

        # K0..K63
        bkIns.extend(K_i)

        # H0..H7
        bkIns.extend(H_i)

        # output H0..H7
        if block == nblocks - 1:
            bkIns.extend(Hout_final)
        else:
            debug("   H_out_0..H_out7 start at input %d" % voffset)
            (tmp, voffset) = alloc(voffset, 8)
            Hout_block.extend(tmp)
            bkIns.extend(tmp)

        # output Hbits0..Hbits7
        debug("   H_out_bits_0[33]..H_out_bits_7[33] start at input %d" % voffset)
        for _ in range(0, 8):
            (tmp, voffset) = alloc(voffset, 33)
            Hout_bits_block.append(tmp)
            bkIns.extend(tmp)

        # initial a,b,c,e,f,g
        bkIns.extend(init_bits)

        # aout_bits and eout_bits
        debug("   {a,e}out_bits(0)[35]..{a,e}out_bits(63)[35] start at input %d" % voffset)
        (tmp, voffset) = alloc(voffset, 35 * 64 * 2)
        bkIns.extend(tmp)

        # finally, r_values
        bkIns.extend(r_values)

        # last thing
        lay_idx += 1

    priv_len = voffset - pub_len
    witness_bits = (priv_len-1).bit_length()
    pad_length = 2 ** witness_bits - pub_len

    # write constants
    fh.write("P V0 = 0 E\n")
    exp = 4
    for i in range(1, v_initial):
        fh.write("P V%d = %d E\n" % (i, exp))
        exp *= 2

    # write public inputs
    ionum = v_initial
    for inVal in inVals[:pub_idx]:
        fh.write("P V%d = I%d E\n" % (inVal, ionum))
        ionum += 1

    # write padding
    if padding:
        for _ in range(0, pad_length):
            fh.write("P V%d = I%d E\n" % (voffset, ionum))
            voffset += 1
            ionum += 1

    # write private inputs
    for inVal in inVals[pub_idx:]:
        fh.write("P V%d = I%d E\n" % (inVal, ionum))
        ionum += 1

    # write pass gates
    expect_ins_len = 7226
    passVals = []
    block_inputs.append(block_inputs[-1]) # even power of 2 invocs
    for bkIns in block_inputs:
        assert len(bkIns) == expect_ins_len + r_values_len
        for outVal in bkIns:
            fh.write("P V%d = V%d PASS V%d E\n" % (voffset, outVal, outVal))
            passVals.append(voffset)
            voffset += 1

    # write out values
    for outVal in passVals:
        fh.write("P O%d = V%d E\n" % (ionum, outVal))
        ionum += 1

    debug("\nPublic inputs are 0--%d" % pub_len)
    debug("r_values start at input %d, length %d" % (r_values_start, r_values_len))
    if padding:
        debug("Added %d dummy inputs for padding" % pad_length)

def get_usage():
    uStr = "Usage: %s [-4] [-m N] [-V]\n\n" % sys.argv[0]

    uStr += " Option    Description                         Default\n"
    uStr += " ------    -----------                         -------\n"
    uStr += " -4        generate 4-round SHA ckt            (False)\n"
    uStr += "           NOTE: can't do Merkle in this case\n\n"

    uStr += " -m n      generate 2^n-leaf Merkle tree RDL   (False)\n\n"

    uStr += " -V        enable verbose mode                 (False)\n\n"

    uStr += " -P        disable padding between x and w     (False)\n"
    uStr += "           in Merkle RDL\n\n"

    uStr += " -R        disable randomized zero test        (False)\n\n"

    uStr += " -C        no consts in sub-AC input list      (False)\n"

    return uStr

if __name__ == "__main__" :
    nrounds = 64
    call = write_64_rounds
    merkle = None
    noconsts = True
    padding = True
    randzero = True
    global VERBOSE
    VERBOSE = False

    uStr = get_usage()
    oStr = "4m:VPRC"
    try:
        (opts, args) = getopt.getopt(sys.argv[1:], oStr)
    except getopt.GetoptError as err:
        print uStr
        print str(err)
        sys.exit(1)
    if len(args) > 0:
        print uStr
        print "ERROR: extraneous arguments."
        sys.exit(1)

    for (opt, arg) in opts:
        if opt == "-4":
            nrounds = 4
            call = write_4_rounds
        elif opt == "-V":
            VERBOSE = True
        elif opt == "-m":
            merkle = int(arg)
        elif opt == "-P":
            padding = False
        elif opt == "-R":
            randzero = False
        elif opt == "-C":
            noconsts = True #we don't want consts and don't need
        else:
            assert False, "logic error: got unexpected option %s from getopt" % opt

    if merkle is not None and nrounds != 64:
        print uStr
        print "ERROR: Merkle can only be used with 64-round ckt"
        sys.exit(1)

    (fd, tempname) = tempfile.mkstemp()
    os.unlink(tempname)
    outname = "SHA256_%d.pws" % nrounds
    with os.fdopen(fd, 'w+') as fh, open(outname, 'w+') as finfh:
        call(fh, finfh, randzero, noconsts)

    #  also write the RDL when nrounds == 4
    if nrounds == 4:
        with open("SHA256_4_rdl.pws", 'w+') as fh:
            write_4_rounds_rdl(fh, randzero)
    elif merkle is not None:
        with open("SHA256_64_merkle_%d_rdl.pws" % merkle, 'w+') as fh:
            write_merkle_rdl(fh, merkle, padding, randzero)

