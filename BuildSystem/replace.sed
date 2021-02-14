
# Super- and subscripts.
#s/\\textasciicircum\([^\}]*\)‿\([^\}]*\)/\$\^\\AgdaFontStyle\{\\scriptscriptstyle \1\}\_\\AgdaFontStyle\{\\scriptscriptstyle \2\}\$/g

s/\\textasciicircum\([^\}]*\)/\{\^\\AgdaFontStyle\{\\scriptscriptstyle \1\}\}/g

#s/‿\([^\}]*\)/\$\_\\AgdaFontStyle\{\\scriptscriptstyle \1\}\$/g

# Σ[ x ∈ X ] into (x : X) ×
s/\\AgdaRecord{Σ\[} \(.*\) \\AgdaRecord{∈} \(.*\) \\AgdaRecord{]}/\\AgdaSymbol\{(\}\1 \\AgdaSymbol\{:\} \2\\AgdaSymbol\{)\} \\AgdaFunction\{×\}/g

# Bind, Kleisli extension and fmap.
#s/>>=/\$\\mathbin\{>\\!\\!\\!>\\mkern-6.7mu=\}\$/g
s/>>=/\\mathbin\{>\\!\\!\\!>\\mkern-6.7mu=\}/g
s/>>/\\mathbin\{>\\!\\!\\!>\}/g
s/>=>/\\mathbin\{>\\mkern-6.7mu=\\mkern-8.3mu>\}/g
#s/=<</\$\\mathbin\{=\\mkern-6.7mu<\\!\\!\\!<\}\$/g
#s/<\\$>/\$\\mathop\{<\\!\\!\\!\\$\\!\\!\\!>\}\$/g
s/<\\$>/\\mathop\{<\\!\\!\\!\\$\\!\\!\\!>\}/g

# Arrow
s/{-}>/\\mathbin\{\\to\}/g

# Append.
s/++/+\\!+/g

# Comments.
#s/AgdaComment{\-\-/AgdaComment\{\-\\!\-/g

# Equality
s/{=}/{\\defeq}/g
s/==/=/g

# Exponentials
# s/{\^}/\{\\widehat\{\}\}/g

s/\^/\\widehat\{\\ \}/g

s/{-}/\{\\textendash\}/g
