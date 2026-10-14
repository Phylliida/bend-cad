# bend-cad spec: the box a plan certifies (DESIGN §8.4). Trusted.
#
# A box gives every variable of a system a center and a radius, numbers of
# a checker's computing numbers K (spec/knum.bend) sent into F by H. A point
# x of F lies in the box when it has one entry per variable and
# |x_v - c_v| <= r_v for every v. A pinned variable has radius 0, so every
# point of the box gives it exactly its center.

import Base
import ./field.bend as O
import ./mat.bend as M
import ./knum.bend as N
import ./cert.bend as C

def inbox(~K: N.Num, ~F: O.OField, ~H: N.Emb<K, F>, +gc: N.KVec(~K), +gr: N.KVec(~K), +x: M.Vec(~F)) -> Data:
  M.Both({M.len(~F, x) == M.len(~F, N.ofkv(~K, ~F, ~H, gc)) : Nat}, C.rbnd(~F, C.vsub(~F, x, N.ofkv(~K, ~F, ~H, gc)), N.ofkv(~K, ~F, ~H, gr)))
