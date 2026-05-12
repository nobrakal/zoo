From zoo Require Import
  prelude.
From zoo.language Require Import
  typeclasses
  notations.
From zoo_std Require Import
  domain.
From zoo Require Import
  options.

Notation "'Null'" := (
  in_type "zoo_saturn.mpmc_bqueue.node" 0
)(in custom zoo_tag
).
Notation "'Node'" := (
  in_type "zoo_saturn.mpmc_bqueue.node" 1
)(in custom zoo_tag
).

Notation next := (  in_type "zoo_saturn.mpmc_bqueue.node.Node" 0
) (only parsing).
Notation "'next'" := (
  in_type "zoo_saturn.mpmc_bqueue.node.Node" 0
)(in custom zoo_field
).
Notation data := (  in_type "zoo_saturn.mpmc_bqueue.node.Node" 1
) (only parsing).
Notation "'data'" := (
  in_type "zoo_saturn.mpmc_bqueue.node.Node" 1
)(in custom zoo_field
).
Notation index := (  in_type "zoo_saturn.mpmc_bqueue.node.Node" 2
) (only parsing).
Notation "'index'" := (
  in_type "zoo_saturn.mpmc_bqueue.node.Node" 2
)(in custom zoo_field
).
Notation estimated_capacity := (  in_type "zoo_saturn.mpmc_bqueue.node.Node" 3
) (only parsing).
Notation "'estimated_capacity'" := (
  in_type "zoo_saturn.mpmc_bqueue.node.Node" 3
)(in custom zoo_field
).

Notation capacity := (  in_type "zoo_saturn.mpmc_bqueue.t" 0
) (only parsing).
Notation "'capacity'" := (
  in_type "zoo_saturn.mpmc_bqueue.t" 0
)(in custom zoo_field
).
Notation front := (  in_type "zoo_saturn.mpmc_bqueue.t" 1
) (only parsing).
Notation "'front'" := (
  in_type "zoo_saturn.mpmc_bqueue.t" 1
)(in custom zoo_field
).
Notation back := (  in_type "zoo_saturn.mpmc_bqueue.t" 2
) (only parsing).
Notation "'back'" := (
  in_type "zoo_saturn.mpmc_bqueue.t" 2
)(in custom zoo_field
).
