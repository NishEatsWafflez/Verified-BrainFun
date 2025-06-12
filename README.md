# BrainFun!
A Verified compiler for the programming language Brainfuck written in Dafny!

The program compiles BF programs into equivalent intermediate representations.

To verify the code:
```
dafny verify *.dfy --verification-time-limit 60
```

If you wish to compile it:

```
dafny build --target:py main.dfy               
```

To run the Python script (AFTER BUILDING)
```
python3 compiler.py                            
```
If something goes wrong, check the path and make sure the transpiled Dafny code is in `main-py`
