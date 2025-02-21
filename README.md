# lrat2dk
Translation of SAT proofs in LRAT format into Dedukti format

## Usage 

```sh
lrat2dk [-o output.dk] [-p header.dk] prefix
```

```prefix.cnf``` contains the problem in DIMACS format.
```prefix.lrat``` contains the proof in LRAT format.
```-o output.dk``` Set output file name (default ```prefix.dk```)
```-p header.dk``` Set name of the included header file (default ```dedukti_prefix```)

## Installation

Requires the ppx_tools package (available for instance via OPAM).

To compile:

```sh
touch .depend 
make
```

