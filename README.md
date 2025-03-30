# Mechanized syntactic soundness proof for $PTR_{atr}$
A reimplementation of the type system by [Siles and Herbelin](https://www.cambridge.org/core/journals/journal-of-functional-programming/article/pure-type-system-conversion-is-always-typable/0BFD4C10E4EBB7884E906982CD1B017F) with Autosubst 2.

The system in this repository has a fixed predicative universe hierarchy, though the confluence theorem is derived from the type exchange property, which holds for general pure type systems. The repository
is still a WIP, but I have already proven the diamond property for the typed parallel reduction relation. 

# Some ideas on $\eta$ rules
- Try proving confluence of $\eta$ for STLC
- Try defining "outer" eta expansion and prove the $\eta$ inversion lemmas (see how I proved and possibly reinvented a similar result for lambda FP)
- Does typing need to be defined directly in terms of parallel reduction?
