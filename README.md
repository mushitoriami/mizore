# mizore
A static analyzer that verifies Python asserts before execution.

```
$ cat example.py
x = 1
assert(x == 1)
assert(x == 2)
$ mizore example.py
Failed to verify the assertion:
assert(x == 2)

$
```
