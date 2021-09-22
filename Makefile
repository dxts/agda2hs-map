.PHONY: default build

default: build

build:
	mkdir -p build
	@echo == Compiling project ==
	agda2hs -o build src/Data/Map/Internal.agda
	agda2hs -o build src/Data/Map'/Internal.agda

try:
	mkdir -p build
	@echo == Compiling file ==
	agda2hs -o build $(path)

haskell: build
	ghc -fno-code build/Data/Map/Internal.hs
