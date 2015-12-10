|buildstatus|

Python reports location only at the granularity of a line
number. Sometimes you would like better or more precise information.

We can get this by uncompiling or deparsing python byte code staring
from a code instruction offset.

This code is based on uncompyle2_.

See also deparse_.


.. _uncompyle2: https://pypi.python.org/pypi/uncompyle2/1.1
.. _deparse: https://github.com/rocky/python-deparse/wiki/Deparsing-technology-and-its-use-in-exact-location-reporting
.. |buildstatus| image:: https://travis-ci.org/rocky/python-deparse.svg
