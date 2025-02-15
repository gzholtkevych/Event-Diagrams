# Event Diagrams

```mermaid

graph BT
    fs[FiniteSets.v] --> root[Enum.v]
    vc[Vocabulary.v] --> fs
    vc[Vocabulary.v] --> root
    dgm[Diagrams.v] --> vc
    co[CausalOrder] --> dgm

```