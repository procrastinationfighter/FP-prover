.PHONY: all

all: FO-prover

FO-prover: FO-prover.hs *.hs
	ghc -O1 -o FO-prover FO-prover.hs -package QuickCheck -package parsec -package random -package extra

clean:
	rm FO-prover *.hi *.o