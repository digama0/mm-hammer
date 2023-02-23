#!/bin/sh
set -e

if ! command -v cargo > /dev/null; then
  echo "You don't seem to have Rust installed."
  echo "Follow the instructions at https://rustup.rs"
  exit 1
fi

if ! command -v sbcl > /dev/null; then
  echo "This installer requires SBCL (the common lisp compiler)."
  echo "Try 'sudo apt insall sbcl' on Debian"
  exit 1
fi

mkdir -p build bin tmp
cd build

if [ ! -d Prover9 ]; then
  echo "Installing Prover9, Vampire and HolyHammer utils"
  git clone https://github.com/ai4reason/Prover9.git
  cd Prover9
  make all
  cd bin
  wget https://github.com/vprover/vampire/releases/download/v4.7/vampire4.7.zip
  unzip vampire4.7.zip
  mv vampire_z3_rel_static_HEAD_6295 ../../../bin/vampire
  wget http://grid01.ciirc.cvut.cz/~mptp/hhutils/hhutils.tar.gz
  tar xzf hhutils.tar.gz
  mv -t . hhutils/*
  mv features tptp_to_ladr predict prooftrans prover9 ../../../bin
  cd ../..
fi

if [ ! -f set.mm ]; then
  echo "Downloading set.mm"
  wget -O set.mm 'https://github.com/metamath/set.mm/blob/d75c0dbe/set.mm?raw=true'
fi

echo "Building mm-hammer"
cargo build --release

if [ ! -f set.lisp ]; then
  echo "Translating set.mm to Lisp"
  ../target/release/mm-hammer set.mm > set.lisp
fi

if [ ! -f ../bin/translate ]; then
  echo "Compiling translate by SBCL"
  sbcl --script ../src/translate.lisp
  mv translate ../bin
fi

echo "Creating first order and higher order TPTP"
mkdir -p bushy-fof bushy-lisp
time ../bin/translate tofof set.lisp set.mm.ax bushy-fof
# real    0m9.711s
# user    0m4.316s
# sys     0m1.011s

# the lisp version for reconstruction
time ../bin/translate tolisp set.lisp set.mm.ax.lisp bushy-lisp
# real    0m5.680s
# user    0m4.330s
# sys     0m0.888s

echo "Exporting features from set.mm.ax"
time ../bin/features -const -trm0 -sub0 -pat 2 -gen set.mm.ax > set.mm.ax.fea
# real    0m10.429s
# user    0m9.420s
# sys     0m0.204s

# create the chronological sequence
cut -f1 -d\, set.mm.ax | cut -f2 -d\(  > set.mm.ax.seq

cd bushy-fof
echo "Exporting proof dependencies for set.mm.ax"
time ../../src/mkdeps1.pl `ls` > ../set.mm.ax.deps
# real    0m1.034s
# user    0m0.834s
# sys     0m0.177s
cd ..

cd ..

echo "Testing mm-hammer with premise selection on a simple chainy problem"
target/release/mm-hammer build/set.mm + example/hllatd.mm hllatd

echo
echo "Done! If you see something like"
echo "   ( chlt wcel clat hllat syl ) ABDEZBFEZCBGH $."
echo "above then it's working."
echo
echo "To run the hammer, use"
echo "  cargo run --release build/set.mm + NEW.mm mythm"
echo "where NEW.mm is a file to be appended to set.mm which has a"
echo "'mythm \$p' theorem in it (the proof is ignored and can be '?')."
