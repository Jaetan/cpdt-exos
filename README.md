This repository contains solutions to a selection of exercises on the subject of programming with dependent types.

# Background

My job is to develop and maintain software. Over the years, as I worked on more and more software, I found that many of the programs I worked on contained the same kinds of bugs: for example, off-by-one errors on collection indices, overflow of the range of a data type, or failure to discriminate between the absence of data and a default value were not rare.

I started thinking that, as software engineers, we ought to be able to do better than repeat these mistakes. Or at least, be able to catch them earlier in the lifetime of the programs. People who care about the quality of the software they write have long been relentlessly testing it, trying to cover the myriad of states any non-trivial program necessarily has. But such coverage can never be complete: the sheer number of test cases, as well as the need to maintain the tests that are written prevent it. Further, there is a type of requirement that is often necessary, but even harder to check: no matter how hard we try, we can not exhaustively test a negative condition, such as "the program never does xxx". Run-time checks, in the form of assertions, help detect that the unwanted condition happened; but then recovery from this state is rarely practical (the condition would not be unwanted otherwise). And there is an important difference between being able to detect that a condition happened during a run of the program, and being confident that such condition never happens.

For a long time I have had an interest in functional programming, and while studying the type systems used by various programming languages, I stumbled upon Adam Chlipala's "Certified Programming with Dependent Types" book, and started reading it.

# Contents

The repository contains the Coq sources for the solutions I found to some exercices in the book, named after the section the exercises appear in. I am using the coq and proof-general packages available in the stable release of the Debian distribution to write these files. To check them, open Emacs, load Proof General, and step through the code to see the proofs unfold.

I am aware that there are shorter proofs, or that some tactics used can be better encapsulated. While learning, though, I chose to dive in the details and get an understanding of what the lower level tactics do, to learn the correspondence between them and the natural deduction rules for the logic Coq implements.

# Intent

This repository is meant to provide a common place to keep my progress through the book, and serve as a backup of the Coq sources on my hard drive. It might be of interest to others, but new content will only be added as I go through more of the book and solve more exercises.
