"""Tests of maps/ssoss_candidate.py and maps/veblen.py: the CANDIDATE value of
SSOSS sequences from (0,0,2) up to below P2 = (0,0,2,1,0,2,1,1). NOT PROVED.

    python3 -m unittest discover -s tests        (from python/trans)

EXPECTED was made with the original evaluator of https://github.com/koteitan/ssosn
(`work/token_value.py`, `value(s)`, flags P1_ROOT_EXPERIMENT,
P1_V_BITS_EXPERIMENT and P2_V7_EXPERIMENT on): every standard form of
[(0,0,2), P1) of length at most 7 and of [P1, P2) of length at most 12, and a
random sample of the other lengths up to 18 (415 sequences). Each line is the
sequence, its value as the source prints it, and the exb term of `to_exb`.
The standard forms come from the greedy descent of the source (`work/std.py`).
These values are a conjecture: the tests check that the port computes the same
values as the source, not that the values are right.
"""

import functools
import os
import subprocess
import sys
import unittest

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
sys.path.insert(0, ROOT)

import maps  # noqa: E402
from maps import ssoss, ssoss_candidate as C, veblen as V  # noqa: E402
from maps.errors import DomainError  # noqa: E402
from notation import exb  # noqa: E402
from notation.exb_std import is_ot, lt  # noqa: E402

EXPECTED = """
002 e0 e0
0020 e0+1 e0+1
00200 e0+2 e0+2
00200000 e0+5 e0+5
002000000 e0+6 e0+6
002001 e0+w e0+w
0020010 e0+w+1 e0+w+1
00200100 e0+w+2 e0+w+2
002001001 e0+w2 e0+w+w
00200101000 e0+w^2+3 e0+p0(2)+3
00200101010101 e0+w^5 e0+p0(5)
00200110 e0+w^w+1 e0+p0(w)+1
0020011001001 e0+w^w+w2 e0+p0(w)+w+w
002001100101000 e0+w^w+w^2+3 e0+p0(w)+p0(2)+3
00200110011 e0+w^w·2 e0+p0(w)+p0(w)
002001101 e0+w^(w+1) e0+p0(w+1)
00200111 e0+w^w^w e0+p0(p0(w))
00200111000 e0+w^w^w+3 e0+p0(p0(w))+3
002001110100100 e0+w^(w^w+1)+w+2 e0+p0(p0(w)+1)+w+2
0020011110 e0+w^w^w^w+1 e0+p0(p0(p0(w)))+1
0020011110111101 e0+w^(w^w^w^2+1) e0+p0(p0(p0(p0(2)))+1)
00200111111 e0+w^w^w^w^w^w e0+p0(p0(p0(p0(p0(w)))))
002002 e0·2 e0+e0
002002001 e0·2+w e0+e0+w
00200200111 e0·2+w^w^w e0+e0+p0(p0(w))
002002002 e0·3 e0+e0+e0
0020020020 e0·3+1 e0+e0+e0+1
0020020020011 e0·3+w^w e0+e0+e0+p0(w)
002002002002002002 e0·6 e0+e0+e0+e0+e0+e0
00201 w^(e0+1) p0(W+1)
002010 w^(e0+1)+1 p0(W+1)+1
00201000 w^(e0+1)+3 p0(W+1)+3
002010000 w^(e0+1)+4 p0(W+1)+4
00201001 w^(e0+1)+w p0(W+1)+w
00201001110 w^(e0+1)+w^w^w+1 p0(W+1)+p0(p0(w))+1
002010020011111001 w^(e0+1)+e0+w^w^w^w^w+w p0(W+1)+e0+p0(p0(p0(p0(w))))+w
00201002002001 w^(e0+1)+e0·2+w p0(W+1)+e0+e0+w
0020100201 w^(e0+1)·2 p0(W+1)+p0(W+1)
00201010 w^(e0+2)+1 p0(W+2)+1
002010100 w^(e0+2)+2 p0(W+2)+2
00201010010 w^(e0+2)+w+1 p0(W+2)+w+1
0020101002 w^(e0+2)+e0 p0(W+2)+e0
0020101002001 w^(e0+2)+e0+w p0(W+2)+e0+w
002010101 w^(e0+3) p0(W+3)
00201010100 w^(e0+3)+2 p0(W+3)+2
00201011 w^(e0+w) p0(W+w)
002010110 w^(e0+w)+1 p0(W+w)+1
0020101100101 w^(e0+w)+w^2 p0(W+w)+p0(2)
0020101101011010 w^(e0+w2+1)+1 p0(W+w+w+1)+1
0020101101100200 w^(e0+w^2)+e0+2 p0(W+p0(2))+e0+2
0020101111110 w^(e0+w^w^w^w^w)+1 p0(W+p0(p0(p0(p0(w)))))+1
00201011111111010 w^(e0+w^w^w^w^w^w^w+1)+1 p0(W+p0(p0(p0(p0(p0(p0(w))))))+1)+1
0020102 w^(e0·2) p0(W+e0)
0020102001 w^(e0·2)+w p0(W+e0)+w
002010200111000 w^(e0·2)+w^w^w+3 p0(W+e0)+p0(p0(w))+3
0020102002010110 w^(e0·2)+w^(e0+w)+1 p0(W+e0)+p0(W+w)+1
002010201 w^(e0·2+1) p0(W+e0+1)
0020102010 w^(e0·2+1)+1 p0(W+e0+1)+1
002010201011 w^(e0·2+w) p0(W+e0+w)
002011 w^w^(e0+1) p0(W+p0(W+1))
00201100110 w^w^(e0+1)+w^w+1 p0(W+p0(W+1))+p0(w)+1
002011002001 w^w^(e0+1)+e0+w p0(W+p0(W+1))+e0+w
00201100200110 w^w^(e0+1)+e0+w^w+1 p0(W+p0(W+1))+e0+p0(w)+1
002011002001111 w^w^(e0+1)+e0+w^w^w^w p0(W+p0(W+1))+e0+p0(p0(p0(w)))
00201101 w^(w^(e0+1)+1) p0(W+p0(W+1)+1)
0020110101 w^(w^(e0+1)+2) p0(W+p0(W+1)+2)
002011011101001100 w^(w^(e0+w)+1)+w^w+2 p0(W+p0(W+w)+1)+p0(w)+2
0020110200 w^w^(e0·2)+2 p0(W+p0(W+e0))+2
0020110201 w^(w^(e0·2)+1) p0(W+p0(W+e0)+1)
0020111000 w^w^w^(e0+1)+3 p0(W+p0(W+p0(W+1)))+3
00201110020100 w^w^w^(e0+1)+w^(e0+1)+2 p0(W+p0(W+p0(W+1)))+p0(W+1)+2
002011101020101 w^(w^w^(e0+1)+e0+2) p0(W+p0(W+p0(W+1))+e0+2)
0020111010201011 w^(w^w^(e0+1)+e0+w) p0(W+p0(W+p0(W+1))+e0+w)
002011101100 w^w^(w^(e0+1)+1)+2 p0(W+p0(W+p0(W+1)+1))+2
00201110111 w^w^w^(e0+2) p0(W+p0(W+p0(W+2)))
002011102 w^w^w^(e0·2) p0(W+p0(W+p0(W+e0)))
0020111020010100 w^w^w^(e0·2)+w^2+2 p0(W+p0(W+p0(W+e0)))+p0(2)+2
0020111020110111 w^w^(w^(e0·2)+w) p0(W+p0(W+p0(W+e0)+w))
0020111020111020 w^w^w^(e0·3)+1 p0(W+p0(W+p0(W+e0+e0)))+1
00201111 w^w^w^w^(e0+1) p0(W+p0(W+p0(W+p0(W+1))))
002011110011011 w^w^w^w^(e0+1)+w^w^2 p0(W+p0(W+p0(W+p0(W+1))))+p0(p0(2))
002011110100111101 w^(w^w^w^(e0+1)+1)+w^(w^w^w+1) p0(W+p0(W+p0(W+p0(W+1)))+1)+p0(p0(p0(w))+1)
00201111010101 w^(w^w^w^(e0+1)+3) p0(W+p0(W+p0(W+p0(W+1)))+3)
0020111101011 w^(w^w^w^(e0+1)+w) p0(W+p0(W+p0(W+p0(W+1)))+w)
0020111101020 w^(w^w^w^(e0+1)+e0)+1 p0(W+p0(W+p0(W+p0(W+1)))+e0)+1
00201111020101000 w^(w^w^w^(e0·2)+2)+3 p0(W+p0(W+p0(W+p0(W+e0)))+2)+3
00201111020111 w^w^w^(w^(e0·2)+1) p0(W+p0(W+p0(W+p0(W+e0)+1)))
00201111101 w^(w^w^w^w^(e0+1)+1) p0(W+p0(W+p0(W+p0(W+p0(W+1))))+1)
0020111111 w^w^w^w^w^w^(e0+1) p0(W+p0(W+p0(W+p0(W+p0(W+p0(W+1))))))
0020111111020 w^w^w^w^w^w^(e0·2)+1 p0(W+p0(W+p0(W+p0(W+p0(W+p0(W+e0))))))+1
00201111111001 w^w^w^w^w^w^w^(e0+1)+w p0(W+p0(W+p0(W+p0(W+p0(W+p0(W+p0(W+1)))))))+w
00201200 e1+2 e1+2
002012001 e1+w e1+w
0020120011110 e1+w^w^w^w+1 e1+p0(p0(p0(w)))+1
002012001111000 e1+w^w^w^w+3 e1+p0(p0(p0(w)))+3
002012002 e1+e0 e1+e0
00201200200111011 e1+e0+w^w^(w+1) e1+e0+p0(p0(w+1))
002012010020 w^(e1+1)+e0+1 p0(W+W+1)+e0+1
002012010100 w^(e1+2)+2 p0(W+W+2)+2
00201201011 w^(e1+w) p0(W+W+w)
00201201011010100 w^(e1+w+2)+2 p0(W+W+w+2)+2
0020120101111011 w^(e1+w^(w^w+1)) p0(W+W+p0(p0(w)+1))
0020120102000 w^(e1+e0)+3 p0(W+W+e0)+3
0020120110 w^w^(e1+1)+1 p0(W+W+p0(W+W+1))+1
002012011001 w^w^(e1+1)+w p0(W+W+p0(W+W+1))+w
00201201111011020 w^w^(w^w^(e1+1)+e0)+1 p0(W+W+p0(W+W+p0(W+W+p0(W+W+1))+e0))+1
00201201111100100 w^w^w^w^w^(e1+1)+w+2 p0(W+W+p0(W+W+p0(W+W+p0(W+W+p0(W+W+1)))))+w+2
002012011111020 w^w^w^w^w^(e1+e0)+1 p0(W+W+p0(W+W+p0(W+W+p0(W+W+p0(W+W+e0)))))+1
002012012010200 w^(e2+e0)+2 p0(W+W+W+e0)+2
00202 e_w p0(p1(1))
002020 e_w+1 p0(p1(1))+1
0020200 e_w+2 p0(p1(1))+2
00202000 e_w+3 p0(p1(1))+3
002020000 e_w+4 p0(p1(1))+4
00202001 e_w+w p0(p1(1))+w
002020010101 e_w+w^3 p0(p1(1))+p0(3)
00202001101000 e_w+w^(w+1)+3 p0(p1(1))+p0(w+1)+3
0020200111101111 e_w+w^w^w^w^2 p0(p1(1))+p0(p0(p0(p0(2))))
00202002 e_w+e0 p0(p1(1))+e0
002020020 e_w+e0+1 p0(p1(1))+e0+1
0020200200 e_w+e0+2 p0(p1(1))+e0+2
00202002002 e_w+e0·2 p0(p1(1))+e0+e0
0020200200200111 e_w+e0·2+w^w^w p0(p1(1))+e0+e0+p0(p0(w))
002020020101000000 e_w+w^(e0+2)+6 p0(p1(1))+p0(W+2)+6
00202002012001 e_w+e1+w p0(p1(1))+e1+w
0020200202 e_w·2 p0(p1(1))+p0(p1(1))
00202010 w^(e_w+1)+1 p0(p1(1)+1)+1
002020100201110111 w^(e_w+1)+w^w^w^(e0+2) p0(p1(1)+1)+p0(W+p0(W+p0(W+2)))
002020101 w^(e_w+2) p0(p1(1)+2)
00202010111111000 w^(e_w+w^w^w^w^w)+3 p0(p1(1)+p0(p0(p0(p0(w)))))+3
002020102 w^(e_w+e0) p0(p1(1)+e0)
002020102011001110 w^(e_w+w^(e0+1))+w^w^w+1 p0(p1(1)+p0(W+1))+p0(p0(w))+1
002020102020100 w^(e_w·2+1)+2 p0(p1(1)+p0(p1(1))+1)+2
00202011 w^w^(e_w+1) p0(p1(1)+p0(p1(1)+1))
002020110 w^w^(e_w+1)+1 p0(p1(1)+p0(p1(1)+1))+1
002020110000 w^w^(e_w+1)+4 p0(p1(1)+p0(p1(1)+1))+4
00202011001111 w^w^(e_w+1)+w^w^w^w p0(p1(1)+p0(p1(1)+1))+p0(p0(p0(w)))
002020110020110 w^w^(e_w+1)+w^w^(e0+1)+1 p0(p1(1)+p0(p1(1)+1))+p0(W+p0(W+1))+1
0020201101011110 w^(w^(e_w+1)+w^w^w)+1 p0(p1(1)+p0(p1(1)+1)+p0(p0(w)))+1
002020110110 w^w^(e_w+2)+1 p0(p1(1)+p0(p1(1)+2))+1
00202011011000000 w^w^(e_w+2)+6 p0(p1(1)+p0(p1(1)+2))+6
002020110110010 w^w^(e_w+2)+w+1 p0(p1(1)+p0(p1(1)+2))+w+1
0020201110 w^w^w^(e_w+1)+1 p0(p1(1)+p0(p1(1)+p0(p1(1)+1)))+1
0020201110020201 w^w^w^(e_w+1)+w^(e_w+1) p0(p1(1)+p0(p1(1)+p0(p1(1)+1)))+p0(p1(1)+1)
002020111010 w^(w^w^(e_w+1)+1)+1 p0(p1(1)+p0(p1(1)+p0(p1(1)+1))+1)+1
00202011101110102 w^(w^w^(e_w+2)+e0) p0(p1(1)+p0(p1(1)+p0(p1(1)+2))+e0)
00202011102 w^w^w^(e_w+e0) p0(p1(1)+p0(p1(1)+p0(p1(1)+e0)))
002020111110102012 w^(w^w^w^w^(e_w+1)+e1) p0(p1(1)+p0(p1(1)+p0(p1(1)+p0(p1(1)+p0(p1(1)+1))))+e1)
00202011111011100 w^w^w^(w^w^(e_w+1)+1)+2 p0(p1(1)+p0(p1(1)+p0(p1(1)+p0(p1(1)+p0(p1(1)+1))+1)))+2
0020201111111011 w^w^(w^w^w^w^w^(e_w+1)+1) p0(p1(1)+p0(p1(1)+p0(p1(1)+p0(p1(1)+p0(p1(1)+p0(p1(1)+p0(p1(1)+1)))))+1))
00202012 e_(w+1) p0(p1(1)+W)
00202012002 e_(w+1)+e0 p0(p1(1)+W)+e0
002020120100111 w^(e_(w+1)+1)+w^w^w p0(p1(1)+W+1)+p0(p0(w))
0020201201020000 w^(e_(w+1)+e0)+4 p0(p1(1)+W+e0)+4
002020120120020 e_(w+2)+e0+1 p0(p1(1)+W+W)+e0+1
0020201202 e_w^2 p0(p1(2))
002020120201 w^(e_w^2+1) p0(p1(2)+1)
00202020 e_w^w+1 p0(p1(w))+1
0020202002011 e_w^w+w^w^(e0+1) p0(p1(w))+p0(W+p0(W+1))
0020202002020100 e_w^w+w^(e_w+1)+2 p0(p1(w))+p0(p1(1)+1)+2
00202020100 w^(e_w^w+1)+2 p0(p1(w)+1)+2
002020201000 w^(e_w^w+1)+3 p0(p1(w)+1)+3
0020202010101 w^(e_w^w+3) p0(p1(w)+3)
00202020102011 w^(e_w^w+w^(e0+1)) p0(p1(w)+p0(W+1))
002020201020111000 w^(e_w^w+w^w^(e0+1))+3 p0(p1(w)+p0(W+p0(W+1)))+3
002020201020120 w^(e_w^w+e1)+1 p0(p1(w)+e1)+1
00202020111002012 w^w^w^(e_w^w+1)+e1 p0(p1(w)+p0(p1(w)+p0(p1(w)+1)))+e1
002020201110101 w^(w^w^(e_w^w+1)+2) p0(p1(w)+p0(p1(w)+p0(p1(w)+1))+2)
0020202011102012 w^w^w^(e_w^w+e1) p0(p1(w)+p0(p1(w)+p0(p1(w)+e1)))
0020202012 e_(w^w+1) p0(p1(w)+W)
00202020120120 e_(w^w+2)+1 p0(p1(w)+W+W)+1
0020202020102001 w^(e_w^w^w+e0)+w p0(p1(p0(w))+e0)+w
002020202020 e_w^w^w^w+1 p0(p1(p0(p0(w))))+1
0021 e_e0 p0(p1(e0))
00210 e_e0+1 p0(p1(e0))+1
002100 e_e0+2 p0(p1(e0))+2
00210000 e_e0+4 p0(p1(e0))+4
002100000 e_e0+5 p0(p1(e0))+5
0021000000 e_e0+6 p0(p1(e0))+6
0021001 e_e0+w p0(p1(e0))+w
00210010 e_e0+w+1 p0(p1(e0))+w+1
002100100 e_e0+w+2 p0(p1(e0))+w+2
002100101 e_e0+w^2 p0(p1(e0))+p0(2)
002100110010 e_e0+w^w+w+1 p0(p1(e0))+p0(w)+w+1
002100110101100100 e_e0+w^(w2)+w+2 p0(p1(e0))+p0(w+w)+w+2
002100111 e_e0+w^w^w p0(p1(e0))+p0(p0(w))
00210011101001 e_e0+w^(w^w+1)+w p0(p1(e0))+p0(p0(w)+1)+w
00210011101101101 e_e0+w^(w^(w+2)+1) p0(p1(e0))+p0(p0(w+2)+1)
00210011111 e_e0+w^w^w^w^w p0(p1(e0))+p0(p0(p0(p0(w))))
002100111110 e_e0+w^w^w^w^w+1 p0(p1(e0))+p0(p0(p0(p0(w))))+1
00210011111110010 e_e0+w^w^w^w^w^w^w+w+1 p0(p1(e0))+p0(p0(p0(p0(p0(p0(w))))))+w+1
0021002 e_e0+e0 p0(p1(e0))+e0
00210020 e_e0+e0+1 p0(p1(e0))+e0+1
002100200 e_e0+e0+2 p0(p1(e0))+e0+2
0021002001 e_e0+e0+w p0(p1(e0))+e0+w
00210020010 e_e0+e0+w+1 p0(p1(e0))+e0+w+1
0021002001101 e_e0+e0+w^(w+1) p0(p1(e0))+e0+p0(w+1)
002100200111 e_e0+e0+w^w^w p0(p1(e0))+e0+p0(p0(w))
0021002010000 e_e0+w^(e0+1)+4 p0(p1(e0))+p0(W+1)+4
0021002010010100 e_e0+w^(e0+1)+w^2+2 p0(p1(e0))+p0(W+1)+p0(2)+2
00210020110101111 e_e0+w^(w^(e0+1)+w^w^w) p0(p1(e0))+p0(W+p0(W+1)+p0(p0(w)))
00210020111010201 e_e0+w^(w^w^(e0+1)+e0+1) p0(p1(e0))+p0(W+p0(W+p0(W+1))+e0+1)
0021002012 e_e0+e1 p0(p1(e0))+e1
00210020201 e_e0+w^(e_w+1) p0(p1(e0))+p0(p1(1)+1)
0021002020100 e_e0+w^(e_w+1)+2 p0(p1(e0))+p0(p1(1)+1)+2
002100202011 e_e0+w^w^(e_w+1) p0(p1(e0))+p0(p1(1)+p0(p1(1)+1))
00210020202020201 e_e0+w^(e_w^w^w^w+1) p0(p1(e0))+p0(p1(p0(p0(w)))+1)
00210021 e_e0·2 p0(p1(e0))+p0(p1(e0))
0021002100101 e_e0·2+w^2 p0(p1(e0))+p0(p1(e0))+p0(2)
002101 w^(e_e0+1) p0(p1(e0)+1)
0021010 w^(e_e0+1)+1 p0(p1(e0)+1)+1
00210100 w^(e_e0+1)+2 p0(p1(e0)+1)+2
0021010000 w^(e_e0+1)+4 p0(p1(e0)+1)+4
002101001 w^(e_e0+1)+w p0(p1(e0)+1)+w
002101001010 w^(e_e0+1)+w^2+1 p0(p1(e0)+1)+p0(2)+1
0021010011001 w^(e_e0+1)+w^w+w p0(p1(e0)+1)+p0(w)+w
002101002 w^(e_e0+1)+e0 p0(p1(e0)+1)+e0
0021010021 w^(e_e0+1)+e_e0 p0(p1(e0)+1)+p0(p1(e0))
00210101 w^(e_e0+2) p0(p1(e0)+2)
0021010100100 w^(e_e0+2)+w+2 p0(p1(e0)+2)+w+2
00210101001010 w^(e_e0+2)+w^2+1 p0(p1(e0)+2)+p0(2)+1
00210101002 w^(e_e0+2)+e0 p0(p1(e0)+2)+e0
002101010020110000 w^(e_e0+2)+w^w^(e0+1)+4 p0(p1(e0)+2)+p0(W+p0(W+1))+4
002101010101 w^(e_e0+4) p0(p1(e0)+4)
002101010101002012 w^(e_e0+4)+e1 p0(p1(e0)+4)+e1
0021010110 w^(e_e0+w)+1 p0(p1(e0)+w)+1
002101011002001 w^(e_e0+w)+e0+w p0(p1(e0)+w)+e0+w
00210101101 w^(e_e0+w+1) p0(p1(e0)+w+1)
0021010111000 w^(e_e0+w^w)+3 p0(p1(e0)+p0(w))+3
00210101111002012 w^(e_e0+w^w^w)+e1 p0(p1(e0)+p0(p0(w)))+e1
002101011110100110 w^(e_e0+w^w^w+1)+w^w+1 p0(p1(e0)+p0(p0(w))+1)+p0(w)+1
00210102 w^(e_e0+e0) p0(p1(e0)+e0)
00210102101 w^(e_e0·2+1) p0(p1(e0)+p0(p1(e0))+1)
002101021010 w^(e_e0·2+1)+1 p0(p1(e0)+p0(p1(e0))+1)+1
002101021010100 w^(e_e0·2+2)+2 p0(p1(e0)+p0(p1(e0))+2)+2
00210102101020 w^(e_e0·2+e0)+1 p0(p1(e0)+p0(p1(e0))+e0)+1
00210110 w^w^(e_e0+1)+1 p0(p1(e0)+p0(p1(e0)+1))+1
002101100 w^w^(e_e0+1)+2 p0(p1(e0)+p0(p1(e0)+1))+2
0021011001 w^w^(e_e0+1)+w p0(p1(e0)+p0(p1(e0)+1))+w
00210110010100100 w^w^(e_e0+1)+w^2+w+2 p0(p1(e0)+p0(p1(e0)+1))+p0(2)+w+2
002101100111111 w^w^(e_e0+1)+w^w^w^w^w^w p0(p1(e0)+p0(p1(e0)+1))+p0(p0(p0(p0(p0(w)))))
0021011002 w^w^(e_e0+1)+e0 p0(p1(e0)+p0(p1(e0)+1))+e0
00210110021002100 w^w^(e_e0+1)+e_e0·2+2 p0(p1(e0)+p0(p1(e0)+1))+p0(p1(e0))+p0(p1(e0))+2
002101101001001 w^(w^(e_e0+1)+1)+w2 p0(p1(e0)+p0(p1(e0)+1)+1)+w+w
00210110100111111 w^(w^(e_e0+1)+1)+w^w^w^w^w^w p0(p1(e0)+p0(p1(e0)+1)+1)+p0(p0(p0(p0(p0(w)))))
00210110101 w^(w^(e_e0+1)+2) p0(p1(e0)+p0(p1(e0)+1)+2)
002101101020020111 w^(w^(e_e0+1)+e0)+w^w^w^(e0+1) p0(p1(e0)+p0(p1(e0)+1)+e0)+p0(W+p0(W+p0(W+1)))
002101101020110011 w^(w^(e_e0+1)+w^(e0+1))+w^w p0(p1(e0)+p0(p1(e0)+1)+p0(W+1))+p0(w)
0021011010201101 w^(w^(e_e0+1)+w^(e0+1)+1) p0(p1(e0)+p0(p1(e0)+1)+p0(W+1)+1)
0021011011001001 w^w^(e_e0+2)+w2 p0(p1(e0)+p0(p1(e0)+2))+w+w
002101101100101 w^w^(e_e0+2)+w^2 p0(p1(e0)+p0(p1(e0)+2))+p0(2)
002101101101 w^(w^(e_e0+2)+1) p0(p1(e0)+p0(p1(e0)+2)+1)
00210110111011002 w^w^(e_e0+w+1)+e0 p0(p1(e0)+p0(p1(e0)+w+1))+e0
00210110111110101 w^(w^(e_e0+w^w^w)+2) p0(p1(e0)+p0(p1(e0)+p0(p0(w)))+2)
00210110202 w^w^(e_e0+e_w) p0(p1(e0)+p0(p1(e0)+p0(p1(1))))
002101102020102010 w^(w^(e_e0+e_w)+e0+1)+1 p0(p1(e0)+p0(p1(e0)+p0(p1(1)))+e0+1)+1
002101110102020100 w^(w^w^(e_e0+1)+e_w+1)+2 p0(p1(e0)+p0(p1(e0)+p0(p1(e0)+1))+p0(p1(1))+1)+2
00210111010210 w^(w^w^(e_e0+1)+e_e0)+1 p0(p1(e0)+p0(p1(e0)+p0(p1(e0)+1))+p0(p1(e0)))+1
002101110110 w^w^(w^(e_e0+1)+1)+1 p0(p1(e0)+p0(p1(e0)+p0(p1(e0)+1)+1))+1
0021011101100 w^w^(w^(e_e0+1)+1)+2 p0(p1(e0)+p0(p1(e0)+p0(p1(e0)+1)+1))+2
00210111011011 w^w^(w^(e_e0+1)+2) p0(p1(e0)+p0(p1(e0)+p0(p1(e0)+1)+2))
0021011102 w^w^w^(e_e0+e0) p0(p1(e0)+p0(p1(e0)+p0(p1(e0)+e0)))
002101110200200 w^w^w^(e_e0+e0)+e0+2 p0(p1(e0)+p0(p1(e0)+p0(p1(e0)+e0)))+e0+2
0021011102011 w^w^(w^(e_e0+e0)+1) p0(p1(e0)+p0(p1(e0)+p0(p1(e0)+e0)+1))
00210111100101 w^w^w^w^(e_e0+1)+w^2 p0(p1(e0)+p0(p1(e0)+p0(p1(e0)+p0(p1(e0)+1))))+p0(2)
00210111101 w^(w^w^w^(e_e0+1)+1) p0(p1(e0)+p0(p1(e0)+p0(p1(e0)+p0(p1(e0)+1)))+1)
00210111101000 w^(w^w^w^(e_e0+1)+1)+3 p0(p1(e0)+p0(p1(e0)+p0(p1(e0)+p0(p1(e0)+1)))+1)+3
002101111011011 w^w^(w^w^(e_e0+1)+2) p0(p1(e0)+p0(p1(e0)+p0(p1(e0)+p0(p1(e0)+1))+2))
00210111110010 w^w^w^w^w^(e_e0+1)+w+1 p0(p1(e0)+p0(p1(e0)+p0(p1(e0)+p0(p1(e0)+p0(p1(e0)+1)))))+w+1
0021011111021 w^w^w^w^w^(e_e0·2) p0(p1(e0)+p0(p1(e0)+p0(p1(e0)+p0(p1(e0)+p0(p1(e0)+p0(p1(e0)))))))
0021012 e_(e0+1) p0(p1(e0)+W)
002101200 e_(e0+1)+2 p0(p1(e0)+W)+2
0021012001 e_(e0+1)+w p0(p1(e0)+W)+w
00210120020010 e_(e0+1)+e0+w+1 p0(p1(e0)+W)+e0+w+1
0021012002001111 e_(e0+1)+e0+w^w^w^w p0(p1(e0)+W)+e0+p0(p0(p0(w)))
00210120100111 w^(e_(e0+1)+1)+w^w^w p0(p1(e0)+W+1)+p0(p0(w))
0021012010021 w^(e_(e0+1)+1)+e_e0 p0(p1(e0)+W+1)+p0(p1(e0))
002101201021 w^(e_(e0+1)+e_e0) p0(p1(e0)+W+p0(p1(e0)))
00210120110000 w^w^(e_(e0+1)+1)+4 p0(p1(e0)+W+p0(p1(e0)+W+1))+4
00210120110111 w^w^(e_(e0+1)+w) p0(p1(e0)+W+p0(p1(e0)+W+w))
002101202001 e_(e0+w^2)+w p0(p1(e0)+p1(2))+w
00210120200110 e_(e0+w^2)+w^w+1 p0(p1(e0)+p1(2))+p0(w)+1
002101202002011 e_(e0+w^2)+w^w^(e0+1) p0(p1(e0)+p1(2))+p0(W+p0(W+1))
002101202010210010 w^(e_(e0+w^2)+e_e0)+w+1 p0(p1(e0)+p1(2)+p0(p1(e0)))+w+1
002101202012 e_(e0+w^2+1) p0(p1(e0)+p1(2)+W)
00210121 e_e_w p0(p1(p0(p1(1))))
002101210 e_e_w+1 p0(p1(p0(p1(1))))+1
002101210000 e_e_w+4 p0(p1(p0(p1(1))))+4
0021012100110101 e_e_w+w^(w+2) p0(p1(p0(p1(1))))+p0(w+2)
002101210011101010 e_e_w+w^(w^w+2)+1 p0(p1(p0(p1(1))))+p0(p0(w)+2)+1
00210121002001101 e_e_w+e0+w^(w+1) p0(p1(p0(p1(1))))+e0+p0(w+1)
00210121010 w^(e_e_w+1)+1 p0(p1(p0(p1(1)))+1)+1
0021012101002 w^(e_e_w+1)+e0 p0(p1(p0(p1(1)))+1)+e0
0021012101202010 w^(e_(e_w+w^3)+1)+1 p0(p1(p0(p1(1)))+p1(3)+1)+1
002102 e_e_w^w p0(p1(p0(p1(w))))
0021020 e_e_w^w+1 p0(p1(p0(p1(w))))+1
00210200 e_e_w^w+2 p0(p1(p0(p1(w))))+2
0021020000000 e_e_w^w+7 p0(p1(p0(p1(w))))+7
00210200111 e_e_w^w+w^w^w p0(p1(p0(p1(w))))+p0(p0(w))
00210200200 e_e_w^w+e0+2 p0(p1(p0(p1(w))))+e0+2
00210200201011100 e_e_w^w+w^(e0+w^w)+2 p0(p1(p0(p1(w))))+p0(W+p0(w))+2
002102002011110 e_e_w^w+w^w^w^w^(e0+1)+1 p0(p1(p0(p1(w))))+p0(W+p0(W+p0(W+p0(W+1))))+1
0021020020120 e_e_w^w+e1+1 p0(p1(p0(p1(w))))+e1+1
002102002012002 e_e_w^w+e1+e0 p0(p1(p0(p1(w))))+e1+e0
002102002101110102 e_e_w^w+w^(w^w^(e_e0+1)+e0) p0(p1(p0(p1(w))))+p0(p1(e0)+p0(p1(e0)+p0(p1(e0)+1))+e0)
00210201 w^(e_e_w^w+1) p0(p1(p0(p1(w)))+1)
002102010021011100 w^(e_e_w^w+1)+w^w^w^(e_e0+1)+2 p0(p1(p0(p1(w)))+1)+p0(p1(e0)+p0(p1(e0)+p0(p1(e0)+1)))+2
002102010101001010 w^(e_e_w^w+3)+w^2+1 p0(p1(p0(p1(w)))+3)+p0(2)+1
0021020102 w^(e_e_w^w+e0) p0(p1(p0(p1(w)))+e0)
00210201020201201 w^(e_e_w^w+e_(w+1)+1) p0(p1(p0(p1(w)))+p0(p1(1)+W)+1)
002102011002020 w^w^(e_e_w^w+1)+e_w+1 p0(p1(p0(p1(w)))+p0(p1(p0(p1(w)))+1))+p0(p1(1))+1
0021020110100 w^(w^(e_e_w^w+1)+1)+2 p0(p1(p0(p1(w)))+p0(p1(p0(p1(w)))+1)+1)+2
0021020110110011 w^w^(e_e_w^w+2)+w^w p0(p1(p0(p1(w)))+p0(p1(p0(p1(w)))+2))+p0(w)
00210201102 w^w^(e_e_w^w+e0) p0(p1(p0(p1(w)))+p0(p1(p0(p1(w)))+e0))
00210201110202 w^w^w^(e_e_w^w+e_w) p0(p1(p0(p1(w)))+p0(p1(p0(p1(w)))+p0(p1(p0(p1(w)))+p0(p1(1)))))
0021020111110101 w^(w^w^w^w^(e_e_w^w+1)+2) p0(p1(p0(p1(w)))+p0(p1(p0(p1(w)))+p0(p1(p0(p1(w)))+p0(p1(p0(p1(w)))+p0(p1(p0(p1(w)))+1))))+2)
0021020120 e_(e_w^w+1)+1 p0(p1(p0(p1(w)))+W)+1
002102012020201000 w^(e_(e_w^w+w^w^(w+1))+1)+3 p0(p1(p0(p1(w)))+p1(p0(w+1))+1)+3
002102012100 e_e_w^(w+1)+2 p0(p1(p0(p1(w+1))))+2
00210202 e_e_w^w^w p0(p1(p0(p1(p0(w)))))
0021020200110000 e_e_w^w^w+w^w+4 p0(p1(p0(p1(p0(w)))))+p0(w)+4
0021020200202 e_e_w^w^w+e_w p0(p1(p0(p1(p0(w)))))+p0(p1(1))
002102020021 e_e_w^w^w+e_e0 p0(p1(p0(p1(p0(w)))))+p0(p1(e0))
00210202012011 w^w^(e_(e_w^w^w+1)+1) p0(p1(p0(p1(p0(w))))+W+p0(p1(p0(p1(p0(w))))+W+1))
002102020202010 w^(e_e_w^w^w^w^w+1)+1 p0(p1(p0(p1(p0(p0(p0(w))))))+1)+1
002102021 e_e_e0 p0(p1(p0(p1(e0))))
002102021001010000 e_e_e0+w^2+4 p0(p1(p0(p1(e0))))+p0(2)+4
002102021002101 e_e_e0+w^(e_e0+1) p0(p1(p0(p1(e0))))+p0(p1(e0)+1)
002102021010201201 w^(e_e_e0+e1+1) p0(p1(p0(p1(e0)))+e1+1)
00210202101110010 w^w^w^(e_e_e0+1)+w+1 p0(p1(p0(p1(e0)))+p0(p1(p0(p1(e0)))+p0(p1(p0(p1(e0)))+1)))+w+1
00210202101200101 e_(e_e0+1)+w^2 p0(p1(p0(p1(e0)))+W)+p0(2)
0021020210201102 w^w^(e_e_e_w+e0) p0(p1(p0(p1(p0(p1(1)))))+p0(p1(p0(p1(p0(p1(1)))))+e0))
002102021020111020 w^w^w^(e_e_e_w+e0)+1 p0(p1(p0(p1(p0(p1(1)))))+p0(p1(p0(p1(p0(p1(1)))))+p0(p1(p0(p1(p0(p1(1)))))+e0)))+1
0021021 z0 z0
00210210 z0+1 z0+1
002102100 z0+2 z0+2
0021021000 z0+3 z0+3
00210210000 z0+4 z0+4
002102100000 z0+5 z0+5
0021021001 z0+w z0+w
00210210010 z0+w+1 z0+w+1
002102100100 z0+w+2 z0+w+2
002102100101 z0+w^2 z0+p0(2)
00210210011 z0+w^w z0+p0(w)
002102100110 z0+w^w+1 z0+p0(w)+1
002102100111 z0+w^w^w z0+p0(p0(w))
0021021002 z0+e0 z0+e0
00210210020 z0+e0+1 z0+e0+1
002102100200 z0+e0+2 z0+e0+2
0021021002001100 z0+e0+w^w+2 z0+e0+p0(w)+2
002102100201 z0+w^(e0+1) z0+p0(W+1)
002102100202 z0+e_w z0+p0(p1(1))
00210210021 z0+e_e0 z0+p0(p1(e0))
002102100210 z0+e_e0+1 z0+p0(p1(e0))+1
00210210021011002 z0+w^w^(e_e0+1)+e0 z0+p0(p1(e0)+p0(p1(e0)+1))+e0
002102100210200100 z0+e_e_w^w+w+2 z0+p0(p1(p0(p1(w))))+w+2
002102101 w^(z0+1) p0(p1(W)+1)
0021021010 w^(z0+1)+1 p0(p1(W)+1)+1
00210210100 w^(z0+1)+2 p0(p1(W)+1)+2
002102101000 w^(z0+1)+3 p0(p1(W)+1)+3
002102101001 w^(z0+1)+w p0(p1(W)+1)+w
002102101002 w^(z0+1)+e0 p0(p1(W)+1)+e0
002102101002020201 w^(z0+1)+w^(e_w^w+1) p0(p1(W)+1)+p0(p1(w)+1)
00210210101 w^(z0+2) p0(p1(W)+2)
002102101010 w^(z0+2)+1 p0(p1(W)+2)+1
00210210101002 w^(z0+2)+e0 p0(p1(W)+2)+e0
002102101011 w^(z0+w) p0(p1(W)+w)
00210210102 w^(z0+e0) p0(p1(W)+e0)
002102101020 w^(z0+e0)+1 p0(p1(W)+e0)+1
002102101021 w^(z0+e_e0) p0(p1(W)+p0(p1(e0)))
0021021011 w^w^(z0+1) p0(p1(W)+p0(p1(W)+1))
00210210110 w^w^(z0+1)+1 p0(p1(W)+p0(p1(W)+1))+1
002102101100 w^w^(z0+1)+2 p0(p1(W)+p0(p1(W)+1))+2
002102101100200 w^w^(z0+1)+e0+2 p0(p1(W)+p0(p1(W)+1))+e0+2
00210210110020010 w^w^(z0+1)+e0+w+1 p0(p1(W)+p0(p1(W)+1))+e0+w+1
002102101101 w^(w^(z0+1)+1) p0(p1(W)+p0(p1(W)+1)+1)
002102101102 w^w^(z0+e0) p0(p1(W)+p0(p1(W)+e0))
0021021011021011 w^w^(z0+e_e0+1) p0(p1(W)+p0(p1(W)+p0(p1(e0))+1))
00210210111 w^w^w^(z0+1) p0(p1(W)+p0(p1(W)+p0(p1(W)+1)))
002102101110 w^w^w^(z0+1)+1 p0(p1(W)+p0(p1(W)+p0(p1(W)+1)))+1
002102101110210210 w^w^w^(z0·2)+1 p0(p1(W)+p0(p1(W)+p0(p1(W)+z0)))+1
002102101111 w^w^w^w^(z0+1) p0(p1(W)+p0(p1(W)+p0(p1(W)+p0(p1(W)+1))))
0021021012 e_(z0+1) p0(p1(W)+W)
00210210120 e_(z0+1)+1 p0(p1(W)+W)+1
002102101200 e_(z0+1)+2 p0(p1(W)+W)+2
002102101201 w^(e_(z0+1)+1) p0(p1(W)+W+1)
0021021012011 w^w^(e_(z0+1)+1) p0(p1(W)+W+p0(p1(W)+W+1))
00210210120120 e_(z0+2)+1 p0(p1(W)+W+W)+1
002102101202 e_(z0+w^(e0+1)) p0(p1(W)+p1(e0+1))
00210210121 e_e_w^(z0+1) p0(p1(W)+p1(p0(p1(W)+p1(z0+1))))
002102101210 e_e_w^(z0+1)+1 p0(p1(W)+p1(p0(p1(W)+p1(z0+1))))+1
002102101210121020 e_e_w^(z0+w)+1 p0(p1(W)+p1(p0(p1(W)+p1(z0+w))))+1
002102102 e_e_w^(z0+e_w) p0(p1(W)+p1(p0(p1(W)+p1(z0+p0(p1(1))))))
0021021020 e_e_w^(z0+e_w)+1 p0(p1(W)+p1(p0(p1(W)+p1(z0+p0(p1(1))))))+1
00210210200 e_e_w^(z0+e_w)+2 p0(p1(W)+p1(p0(p1(W)+p1(z0+p0(p1(1))))))+2
002102102000 e_e_w^(z0+e_w)+3 p0(p1(W)+p1(p0(p1(W)+p1(z0+p0(p1(1))))))+3
002102102001 e_e_w^(z0+e_w)+w p0(p1(W)+p1(p0(p1(W)+p1(z0+p0(p1(1))))))+w
002102102002 e_e_w^(z0+e_w)+e0 p0(p1(W)+p1(p0(p1(W)+p1(z0+p0(p1(1))))))+e0
00210210201 w^(e_e_w^(z0+e_w)+1) p0(p1(W)+p1(p0(p1(W)+p1(z0+p0(p1(1)))))+1)
002102102010 w^(e_e_w^(z0+e_w)+1)+1 p0(p1(W)+p1(p0(p1(W)+p1(z0+p0(p1(1)))))+1)+1
00210210201001 w^(e_e_w^(z0+e_w)+1)+w p0(p1(W)+p1(p0(p1(W)+p1(z0+p0(p1(1)))))+1)+w
002102102011 w^w^(e_e_w^(z0+e_w)+1) p0(p1(W)+p1(p0(p1(W)+p1(z0+p0(p1(1)))))+p0(p1(W)+p1(p0(p1(W)+p1(z0+p0(p1(1)))))+1))
002102102012 e_(e_w^(z0+e_w)+1) p0(p1(W)+p1(p0(p1(W)+p1(z0+p0(p1(1)))))+W)
00210210201210011 e_e_w^(z0+e_w+1)+w^w p0(p1(W)+p1(p0(p1(W)+p1(z0+p0(p1(1))+1))))+p0(w)
00210210202 e_e_w^(z0+e_w^w) p0(p1(W)+p1(p0(p1(W)+p1(z0+p0(p1(w))))))
002102102020 e_e_w^(z0+e_w^w)+1 p0(p1(W)+p1(p0(p1(W)+p1(z0+p0(p1(w))))))+1
002102102021 e_e_w^(z0+e_e0) p0(p1(W)+p1(p0(p1(W)+p1(z0+p0(p1(e0))))))
0021021021 h0 p0(p1(W+W))
00210210210 h0+1 p0(p1(W+W))+1
002102102100 h0+2 p0(p1(W+W))+2
002102102101 w^(h0+1) p0(p1(W+W)+1)
0021021021010 w^(h0+1)+1 p0(p1(W+W)+1)+1
002102102102 e_e_w^(h0+z_w) p0(p1(W+W)+p1(p0(p1(W+W)+p1(p0(p1(W+W))+p0(p1(W+1))))))
0021021021021 phi(4,0) p0(p1(W+W+W))
0021021021021021 phi(5,0) p0(p1(W+W+W+W))
"""


def rows():
    for line in EXPECTED.split('\n'):
        if line.strip():
            s, v, e = line.split()
            yield tuple(int(c) for c in s), v, e


class TestPort(unittest.TestCase):
    def test_expected(self):
        """The port gives the values of the source on the 415 sequences."""
        n = 0
        for s, v, e in rows():
            self.assertTrue(C.is_standard(s), s)
            self.assertEqual(V.show(C.value(s)), v, s)
            self.assertEqual(exb.show(C.ssoss_candidate_to_exb(s)), e, s)
            n += 1
        self.assertEqual(n, 415)

    def test_named(self):
        cases = {(0, 0, 2): ('e0', 'e0'),
                 (0, 0, 2, 1, 0, 2): ('e_e_w^w', 'p0(p1(p0(p1(w))))'),
                 (0, 0, 2, 1, 0, 2, 1): ('z0', 'z0'),
                 (0, 0, 2, 1, 0, 2, 1, 0, 2, 1): ('h0', 'p0(p1(W+W))')}
        for s, (v, e) in cases.items():
            self.assertEqual(V.show(C.value(s)), v)
            self.assertEqual(exb.show(C.ssoss_candidate_to_exb(s)), e)

    def test_anchor(self):
        """The P1 V anchor: o(P V) = e_(e_(e_0)), P = (0,0,2,1,0,2)."""
        self.assertEqual(V.show(C.value((0, 0, 2, 1, 0, 2, 0, 2, 1))), 'e_e_e0')

    def test_order(self):
        """The values increase with the sequences (lexicographic order)."""
        prev = None
        for s, _, _ in rows():
            x = C.value(s)
            if prev is not None:
                self.assertTrue(V.lt(prev, x), s)
            prev = x

    def test_limits(self):
        """The audit of the source, on EXPECTED: o(S[n]) < o(S) for n = 1..4,
        and o(S 0) = o(S) + 1."""
        for s, _, _ in rows():
            if s[-1] == 0:
                self.assertEqual(C.value(s), V.succ(C.value(s[:-1])), s)
                continue
            for n in range(1, 5):
                t = ssoss.fs(s, n)
                if t >= C.LOW:
                    self.assertTrue(V.lt(C.value(t), C.value(s)), (s, n))

    def test_below_002(self):
        """Below (0,0,2) the source evaluator agrees with the proved value `o`."""
        for s in ssoss.standard_forms(range(5), (1, 2, 3), 12, 10):
            if len(s) >= 2:
                self.assertEqual(V.to_exb(C.value(s)), ssoss.o(s), s)


class TestDomain(unittest.TestCase):
    def test_refused(self):
        for s in ((0, 0, 1, 1),                     # below (0,0,2): the proved o
                  (0, 0, 2, 1, 1), (0, 0, 2, 1, 0, 2, 1, 1), (0, 0, 3),   # not below P2
                  (0, 1, 2), (1, 0, 2),             # not (0,0) first
                  (0, 0, 2, 1, 0, 2, 0, 0, 0, 1)):  # P Z Z L1: not standard
            with self.assertRaises(DomainError, msg=s):
                C.ssoss_candidate_to_exb(s)

    def test_standard(self):
        """The greedy descent on a few sequences of [(0,0,2), P2)."""
        self.assertTrue(C.is_standard((0, 0, 2, 1, 0, 2, 1, 0, 2, 1)))
        self.assertFalse(C.is_standard((0, 0, 2, 1, 0, 2, 0, 0, 0, 1)))
        self.assertFalse(C.is_standard(C.P2))       # P2 is a bound, not a standard form


class TestToExb(unittest.TestCase):
    def test_shorthands(self):
        for n in range(6):
            self.assertEqual(V.to_exb(V.P(V.ONE, V.nat(n))), exb.eps(n))
            self.assertEqual(V.to_exb(V.P(V.nat(2), V.nat(n))), exb.zeta(n))
            self.assertEqual(V.to_exb(V.nat(n)), exb.numeral(n))
        self.assertEqual(V.to_exb(V.OMEGA), exb.OMEGA)
        E = exb.parse
        self.assertEqual(V.to_exb(V.w(V.succ(V.P(V.ONE, ())))), E('p0(W+1)'))   # w^(e0+1)
        self.assertEqual(V.to_exb(V.P(V.nat(3), ())), E('p0(p1(W+W))'))          # eta0
        self.assertEqual(V.to_exb(V.P(V.ONE, V.succ(V.P(V.nat(2), ())))),
                         E('p0(p1(W)+W)'))                                        # e_(z0+1)

    def test_out_of_range(self):
        with self.assertRaises(V.OutOfRange):
            V.to_exb(V.P(V.OMEGA, ()))

    def test_order_family(self):
        """to_exb is standard and keeps the order on a family of ordinals below phi(w, 0)."""
        xs = {(), V.ONE, V.OMEGA}
        for r in range(3):
            ys = set(xs)
            for x in xs:
                for k in range(4):
                    ys.add(V.P(V.nat(k), x))
                for y in xs:
                    if r < 2 or len(x) + len(y) <= 2:
                        ys.add(V.add(x, y))
            xs = ys
        xs = sorted(xs, key=functools.cmp_to_key(V.cmp))
        ts = [V.to_exb(x) for x in xs]
        self.assertGreater(len(xs), 1000)
        for t in ts:
            self.assertTrue(is_ot(t), exb.show(t))
        for a, b in zip(ts, ts[1:]):
            self.assertTrue(lt(a, b), (exb.show(a), exb.show(b)))


class TestPath(unittest.TestCase):
    def test_default_is_proved_only(self):
        with self.assertRaises(DomainError) as cm:
            maps.convert('ssoss', 'exb', (0, 0, 2))
        self.assertIn('--candidate', str(cm.exception))
        _, path = maps.convert('ssoss', 'exb', (0, 0, 1, 1))
        self.assertEqual([e.name for e in path], ['o'])

    def test_candidate(self):
        x, path = maps.convert('ssoss', 'exb', (0, 0, 2, 1, 0, 2, 1), candidate=True)
        self.assertEqual((exb.show(x), [e.name for e in path]), ('z0', ['o?']))
        self.assertTrue(maps.is_candidate(path))
        _, path = maps.convert('ssoss', 'exb', (0, 0, 1, 1), candidate=True)
        self.assertEqual([e.name for e in path], ['o'])     # the proved map first
        self.assertFalse(maps.is_candidate(path))

    def test_cli(self):
        def run(*args):
            return subprocess.run([sys.executable, os.path.join(ROOT, 'trans')] + list(args),
                                  capture_output=True, text=True)
        r = run('--from', 'ssoss', '--to', 'exb', '(0,0,2)')
        self.assertEqual((r.returncode, r.stdout), (1, ''))
        r = run('--candidate', '--from', 'ssoss', '--to', 'exb', '(0,0,2,1,0,2,1)')
        self.assertEqual((r.returncode, r.stdout), (0, 'z0\n'))
        self.assertIn('candidate value, not proved', r.stderr)
        r = run('--candidate', '--from', 'ssoss', '--to', 'exb', '(0,0,1,1)')
        self.assertEqual((r.returncode, r.stdout, r.stderr), (0, 'p0(w)\n', ''))


if __name__ == '__main__':
    unittest.main()
