

#################################################
# The default target
all: FTTA.pdf

# Pipeline: .lagda --Agda--> .tex --SED--> tex --XETEX--> .pdf

# D = Directory
# F = File
# N = Name
# XX = list of X

D_Frame     = ../Frame/
D_FrameTex  = ../Build/Tex/Frame/
D_FramePost = ../Build/Post/Frame/

D_SourceBase = ../Source/
D_Source     = ../Source/TypeTheory/Lambda/
D_SourceTex  = ../Build/Tex/Source/
D_SourcePost = ../Build/Post/Source/

F_SedFile = replace.sed

# D_Output = ../Build/Output/
D_Output = $(D_FramePost)


#################################################
# Build frame

NN_Frame = FTTA.tex main.bib 0-title.tex 1-introduction.tex \
		       5-lambda-calc.tex 5-typechecker.tex 6-interpretation.tex \
					 7-conclusion.tex Z-Declaration.tex uni.png

FF_FramePost = $(patsubst %,$(D_FramePost)%,$(NN_Frame))

$(D_FramePost)%: $(D_Frame)%
	mkdir -p $(dir $@)
	cp $^ $@

bib:
	cd $(D_FramePost) ; \
	bibtex FTTA


# NN_Frame  = FTTA

# FF_FrameTex  = $(patsubst %,$(D_FrameTex)%.tex,$(NN_Frame))
# FF_FramePost = $(patsubst %,$(D_FramePost)%.tex,$(NN_Frame))

# $(D_FrameTex)%.tex: $(D_Frame)%.lagda
# 	cd $(D_Frame) ; \
# 	agda --latex $^ --latex-dir=$(D_FrameTex)

# $(D_FramePost)%.tex: $(D_FrameTex)%.tex
# 	mkdir -p $(dir $@)
# 	sed -f $(F_SedFile) $^ > $@


#################################################
# Build source

NN_Source  = Introduction/Introduction Introduction/Nat \
					   Base/Fin Base/FList Base/Either Base/Fir Base/Category Base/CCC Base/CCCid Base/CCCProofs \
						 Param IParam Core/Type Core/Term Core/TermSub Core/TermSingSub Core/TermProofs \
					   Typing/Error Typing/Checker Typing/CheckerProofs Typing/CheckerSubProofs Typing/CheckerSingSubProofs \
						 Reduction/Beta Reduction/NormalForm Reduction/NormalFormProofs Reduction/Examples \
						 Interpretation/Interpretation Interpretation/InterpretationProofsWeak Interpretation/InterpretationProofsBeta

FF_SourceTex  = $(patsubst %,$(D_SourceTex)TypeTheory/Lambda/%.tex,$(NN_Source))
FF_SourcePost = $(patsubst %,$(D_SourcePost)TypeTheory/Lambda/%.tex,$(NN_Source))

$(D_SourceTex)%.tex: $(D_SourceBase)%.lagda $(F_SedFile)
	cd $(D_SourceBase) ; \
  agda --latex $< --latex-dir=$(D_SourceTex)
#agda --latex $< --only-scope-checking --latex-dir=$(D_SourceTex)

$(D_SourcePost)%.tex: $(D_SourceTex)%.tex
	mkdir -p $(dir $@)
	sed -f $(F_SedFile) $^ > $@


#################################################
# Generate pdf


FTTA.pdf: $(FF_FramePost) $(FF_SourcePost) $(F_SedFile)
	xelatex -include-directory=$(D_Frame) -output-directory=$(D_Output) $^


#################################################
# Special targets


.SECONDARY: $(FF_FrameTex) $(FF_SourceTex)

.PHONY: all bib

