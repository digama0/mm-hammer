# Metamath hammer

This is a tool for running Vampire and Prover9 on metamath problems,
and reconstructing them into a valid metamath proof that can be copied
into the .mm file.

To get started, you will need Rust (https://rustup.rs) and [SBCL](https://www.sbcl.org/)
(`sudo apt install sbcl` on Debian). Then run make.sh:

```shell
$ ./make.sh
...
Testing mm-hammer with premise selection on a simple chainy problem
hllatd
Learning done; awaiting your features ...
0.83user 0.05system 0:00.89elapsed 100%CPU (0avgtext+0avgdata 332728maxresident)k
0inputs+32outputs (0major+84877minor)pagefaults 0swaps
      ( chlt wcel clat hllat syl ) ABDEZBFEZCBGH $.

Done! If you see something like
   ( chlt wcel clat hllat syl ) ABDEZBFEZCBGH $.
above then it's working.

To run the hammer, use
  cargo run --release build/set.mm + NEW.mm mythm
where NEW.mm is a file to be appended to set.mm which has a
'mythm $p' theorem in it (the proof is ignored and can be '?').
```

The install script does a test run at the end, which you can see above.
You can run it yourself with:
```shell
$ cargo run --release build/set.mm + example/hlopdNEW.mm hlopdNEW 2> /dev/null
      ( chlt wcel cops hlop syl ) ABDEZBFEZCBGH $.
```
Here `hlopdNEW.mm` contains just a theorem statement:
```
  ${
    hlopdNEW.1 $e |- ( ph -> K e. HL ) $.
    $( Deduction version of ~ hlop .
       (Contributed by Prover9, 23-Feb-2023.) $)
    hlopdNEW $p |- ( ph -> K e. OP ) $=
      ? $.
  $}
```
The program spits out a proof block that you can paste in to replace the
`?` here.
