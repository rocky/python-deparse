|buildstatus|

Python reports location only at the granularity of a line
number. Sometimes you would like better or more precise information.

We can get this by uncompiling or deparsing python byte code staring
from a code instruction offset.

This code is based on uncompyle.

See also deparse_.


.. _deparse: http://blogs.perl.org/users/rockyb/2015/11/exact-perl-location-with-bdeparse-and-develcallsite.html
.. |buildstatus| image:: https://travis-ci.org/rocky/python-deparse.svg
