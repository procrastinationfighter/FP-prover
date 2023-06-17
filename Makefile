.PHONY: all

all: FO-prover

FO-prover: FO-prover.hs *.hs
	ghc -o FO-prover FO-prover.hs -package QuickCheck -package parsec -package random

clean:
	rm FO-prover *.hi *.o