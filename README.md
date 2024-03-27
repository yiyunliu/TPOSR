# Mechanized syntactic soundness proof for $PTR_{atr}$
A reimplementation of the type system by [Siles and Herbelin](https://www.cambridge.org/core/journals/journal-of-functional-programming/article/pure-type-system-conversion-is-always-typable/0BFD4C10E4EBB7884E906982CD1B017F) with Autosubst 2.

The system in this repository has a fixed predicative universe hierarchy, though the confluence theorem is derived from the type exchange property, which holds for general pure type systems. The repository
is still a WIP, but I have already proven the diamond property for the typed parallel reduction relation. 
