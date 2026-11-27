"""Experimental finite-bit certificate checker; not deployed in the SAT solver.

The abstract cardinality argument is in FibreCardinality.lean. Connecting this
Python code and its integer bit masks to that formal model remains separate.
"""


def parity(x):
    return x.bit_count() % 2 if hasattr(int, 'bit_count') else bin(x).count('1') % 2


def project(x, rows):
    return sum(parity(x & row) << i for i, row in enumerate(rows))


def verify(width, forbidden, images, rows, columns):
    if type(width) is not int or not 0 <= width <= 4096:
        return False
    if not all(isinstance(s, (list, tuple)) for s in [forbidden, images, rows, columns]):
        return False
    d = len(rows)
    if d > width or len(columns) != d:
        return False
    if any(type(x) is not int or not 0 <= x < 1 << width for x in list(forbidden)+list(rows)+list(columns)):
        return False
    if any(type(x) is not int or not 0 <= x < 1 << d for x in images):
        return False
    if len(set(forbidden)) != len(forbidden) or len(set(images)) != len(images):
        return False
    if any(project(column, rows) != 1 << j for j, column in enumerate(columns)):
        return False
    allowed = set(images)
    if any(project(x, rows) not in allowed for x in forbidden):
        return False
    return len(forbidden) == len(images) * (1 << (width-d))
