"""Maps that exist only as the Python programs of Googology/Trans/BMS/PoR/.

The programs are run as they are, in a subprocess, because each of them puts
its own directory on sys.path and imports its neighbours by short names.

- por1     Googology/Trans/BMS/PoR/PSS/por/phi.py        pair sequence -> R1+ pattern
- wilken1  Googology/Trans/BMS/PoR/PSS/por/tr.py         pair sequence -> Wilken T^1
           (the same map as Lean `trNode`, Googology/Trans/BMS/PoR/PSS/TR/Defs.lean:81)
- por2     Googology/Trans/BMS/PoR/Trio/por/phi3def2.py  trio sequence -> pattern of order 2
- wilken2  Googology/Trans/BMS/PoR/Trio/por/tr3.py       trio sequence -> Wilken R2 term
"""

import os
import subprocess
import sys

from .errors import DomainError
from notation import matrix

REPO = os.path.dirname(os.path.dirname(os.path.dirname(os.path.dirname(
    os.path.abspath(__file__)))))
POR = os.path.join(REPO, 'Googology', 'Trans', 'BMS', 'PoR')


def _run(sub, script, m, arrow):
    path = os.path.join(POR, sub, 'por', script)
    arg = matrix.show(m)
    r = subprocess.run([sys.executable, path, arg], capture_output=True, text=True,
                       cwd=os.path.dirname(path))
    if r.returncode != 0 or not r.stdout.strip():
        err = r.stderr.strip().splitlines()
        raise DomainError('%s failed on %s: %s' % (script, arg, err[-1] if err else 'no output'))
    line = r.stdout.splitlines()[0]
    if arrow:
        head = arg + ' -> '
        if not line.startswith(head):
            raise DomainError('%s: unexpected output %r' % (script, line))
        line = line[len(head):]
    return line.strip()


def bms2_to_por1(m):
    return _run('PSS', 'phi.py', m, True)


def bms2_to_wilken1(m):
    return _run('PSS', 'tr.py', m, True)


def bms3_to_por2(m):
    return _run('Trio', 'phi3def2.py', m, False)


def bms3_to_wilken2(m):
    return _run('Trio', 'tr3.py', m, True)
