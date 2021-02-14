
# Formalization of Type Theory in Agda

## Structure
These directories contain the code and text of my bachelor thesis.
For the sake of completeness, all neccessary files for generating a
pdf are also included.

## Generating a pdf
The folder ```Frame``` contains pure LaTeX code, for example the introduction
and the conclusion of the thesis.
The folder ```BuildSystem``` contains a Makefile which can be run to
produce a pdf. All intermediate files are generated in the ```Build``` folder.

## Checking the code with Agda
The main code is in the ```Source/TypeTheory/Lambda``` directory. It is
structured similarly to the chapters:

 - chapter 2: ```Introduction```
 - chapters 3 and 4: ```Base```
 - chapter 5:
    - Types and Terms: ```Core```
    - Typechecker: ```Typing```
    - Reduction and Normalization: ```Reduction```
 - chapter 6: ```Interpretation```
    
The proof of soundness, which recursively includes all other files (except examples),
is contained in the file ```Interpretation/InterpretationProofsBeta.lagda```.
This means that, in order to check the whole code, it is sufficient to run
```
agda TypeTheory/Lambda/Interpretation/InterpretationProofsBeta.lagda
```
(The command _has_ to be run from the ```Source``` directory.)

This typechecks all files: If it is successfull, the only output are the filenames.
Else, errors would be shown.

Typechecking some of the more complex files (mostly in ```Interpretation```), may take
a few minutes and several gigabyte of memory (on my computer: ~5min and ~3GB respectively).

## Obtaining Agda
For verifying, a recent build of Agda has to be used. This can be done either
using the included executable for Windows, or by compiling Agda from its git repository.

### Included executable
The included Windows executable is in the ```Source``` folder.

### Compiling Agda
For this, the following steps need to be taken:
1. Clone the git repo: ```git clone https://github.com/agda/agda```
2. Checkout the correct commit: ```cd agda && git checkout fe6337817cd295f1b7a928b4865f1```
3. Agda is written in Haskell, therefore a Haskell compiler is needed. The easiest
   way for installing it is using stack
   (https://docs.haskellstack.org/en/stable/README/).

   As noted there, the command for installing it is:
   ```curl -sSL https://get.haskellstack.org/ | sh```
4. Using ```stack setup --stack-yaml stack-8.2.2.yaml```, stack installs the correct
   Haskell compiler for Agda.
5. With ```stack build --stack-yaml stack-8.2.2.yaml```, the project can then be build.

When finished, the Agda executable can be found in ```.stack_work/[hash]/bin```.

Alternatively, it can be copied to a global system location using
```stack install --stack-yaml stack-8.2.2.yaml```.

Now the Agda executable can be used to check the code, as described above.


   
   












