
0. History
2022/8/1	First edition

1. Introduction
This project is a branch project from VFCS, which focused on different matrix
formalization techonolgies.
There are at least five FMLs (Formal Matrix Library) exist in Coq community,
although Coq standard library havn't supply it.

Too many choices is not a good news. The users have no idea to choose which one.
Another bad news, once you chosen a library, switching to another one in later
stage is higer expensive, owing to almost completely different definitions and
theorems of these implementations.

So, we give a short comparison study to these models.
And, finally, we give a unified signature, and give implementations for all
these libraries.

Use this unified signature, your code will be more robust and portable.


2. Building instructions
For build,
$ make
or
$ make -j8

For clean,
$ make clean
or
$ make cleanall


3. Known issues
(1) Coq-8.13 and Coq-8.16 has a minor difference when naming parameters.
	Default code style is followed the Coq-8.13.
	If you compile fail in Coq-8.16, a bit piece of code need to be changed.
	The details will be given later.

4. Publication
Integration of Multiple Formal Matrix Models in Coq, SETTA 2022.
there is a local copy "./doc/matrix-coq-setta2022.pdf"




