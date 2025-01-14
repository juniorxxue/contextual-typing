Paper: *Contextual Typing*. Appeared at ICFP 2024

Also check our [online Agda code](https://types.hk/proof/contextual/README.html), [extended version of paper](./paper_extended.pdf) , [zenodo (docker image)](https://zenodo.org/records/11429428), [paper correspondence](./Correspondence.md) and [ICFP talk video](https://youtu.be/U-Aiupk_3u0?si=vB5m6ya1KMluBYOv).

**Abstract**

>Bidirectional typing is a simple, lightweight approach to type inference that propagates known type information
>during typing, and can scale up to many diﬀerent type systems and features. It typically only requires a
>reasonable amount of annotations and eliminates the need for many obvious annotations. Nonetheless the
>power of inference is still limited, and complications arise in the presence of more complex features.
>
>In this paper we present a generalization of bidirectional typing called contextual typing. In contextual
>typing not only known type information is propagated during typing, but also other known information about
>the surrounding context of a term. This information can be of various forms, such as other terms or record
>labels. Due to this richer notion of contextual information, less annotations are needed, while the approach
>remains lightweight and scalable. For type systems with subtyping, contextual typing subsumption is also
>more expressive than subsumption with bidirectional typing, since partially known contextual information
>can be exploited. To aid specifying type systems with contextual typing, we introduce Quantitative Type
>Assignment Systems (QTASs). A QTAS quantifies the amount of type information that a term needs in order
>to type check using counters. Thus, a counter in a QTAS generalizes modes in traditional bidirectional typing,
>which can only model an all (checking mode) or nothing (inference mode) approach. QTASs enable precise
>guidelines for annotatability of contextual type systems formalized as a theorem. We illustrate contextual
>typing first on a simply typed lambda calculus, and then on a richer calculus with subtyping, intersection
>types, records and overloading. All the metatheory is formalized in the Agda theorem prover.

**Quick Build**

Just run:


```
agda README.agda
```

We also provide the command to generate the nicely rendered html files:

```
agda --html README.agda --css "../css/Agda.css"
```
