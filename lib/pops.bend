# bend-cad: what the proposer computes with besides the checker's numbers
# (spec/knum.bend): rounding, the rare operations through S.D, and the
# conversions with S.D. Untrusted. lib/gnumer.bend is numer.bend's proposer
# written once over any K with such operations W; with laws R relating K to
# KI.dnum() (a map of computing numbers, lib/khom.bend, and each operation
# sending the images of S.D values to the images of numer's results), it
# returns exactly numer's plan, mapped (lib/gnumerpf.bend). The word
# dyadics are one such K (lib/wnum.bend: wops; lib/wnumpf.bend: wlaws), for
# every base (PLAN-sk13w W4).

import Base
import ../spec/num.bend as S
import ../spec/knum.bend as N
import ./kinst.bend as KI
import ./numer.bend as NU
import ./khom.bend as KH

type POps<-K: N.Num> is Type:
  POps{ofd: S.D -> N.NC(K),
    tod: N.NC(K) -> S.D,
    sig: N.NC(K) -> Nat -> N.NC(K),
    round: N.NC(K) -> Nat -> N.NC(K),
    sdiv: Nat -> N.NC(K) -> N.NC(K) -> N.NC(K),
    sigup: N.NC(K) -> Nat -> N.NC(K)}

# S.D into K
def ofd(-K: N.Num, W: POps<K>) -> S.D -> N.NC(K):
  match W:
    case POps{ofd, tod, sig, round, sdiv, sigup}:
      ofd

# K back to S.D
def tod(-K: N.Num, W: POps<K>) -> N.NC(K) -> S.D:
  match W:
    case POps{ofd, tod, sig, round, sdiv, sigup}:
      tod

# numer's dsig: about b significant bits
def sig(-K: N.Num, W: POps<K>) -> N.NC(K) -> Nat -> N.NC(K):
  match W:
    case POps{ofd, tod, sig, round, sdiv, sigup}:
      sig

# numer's dround: to a multiple of 2^-p
def round(-K: N.Num, W: POps<K>) -> N.NC(K) -> Nat -> N.NC(K):
  match W:
    case POps{ofd, tod, sig, round, sdiv, sigup}:
      round

# numer's dsdiv: a / b at w significant bits
def sdiv(-K: N.Num, W: POps<K>) -> Nat -> N.NC(K) -> N.NC(K) -> N.NC(K):
  match W:
    case POps{ofd, tod, sig, round, sdiv, sigup}:
      sdiv

# numer's dsigup: up to about b significant bits
def sigup(-K: N.Num, W: POps<K>) -> N.NC(K) -> Nat -> N.NC(K):
  match W:
    case POps{ofd, tod, sig, round, sdiv, sigup}:
      sigup

# h : KI.dnum() -> K, ofd its map, tod a left inverse of it, and every
# operation of W numer's on the images
type PLaws<-K: N.Num, -W: POps<K>> is Type:
  PLaws{hom: KH.Hom<KI.dnum(), K>,
    l_ofd: @x: S.D -> {ofd(K, W, x) == KH.hmap(KI.dnum(), K, hom, x) : N.NC(K)},
    l_tod: @x: S.D -> {tod(K, W, KH.hmap(KI.dnum(), K, hom, x)) == x : S.D},
    l_sig: @x: S.D -> @b: Nat -> {sig(K, W, KH.hmap(KI.dnum(), K, hom, x), b) == KH.hmap(KI.dnum(), K, hom, NU.dsig(x, b)) : N.NC(K)},
    l_round: @x: S.D -> @p: Nat -> {round(K, W, KH.hmap(KI.dnum(), K, hom, x), p) == KH.hmap(KI.dnum(), K, hom, NU.dround(x, p)) : N.NC(K)},
    l_sdiv: @w: Nat -> @a: S.D -> @b: S.D -> {sdiv(K, W, w, KH.hmap(KI.dnum(), K, hom, a), KH.hmap(KI.dnum(), K, hom, b)) == KH.hmap(KI.dnum(), K, hom, NU.dsdiv(w, a, b)) : N.NC(K)},
    l_sigup: @x: S.D -> @b: Nat -> {sigup(K, W, KH.hmap(KI.dnum(), K, hom, x), b) == KH.hmap(KI.dnum(), K, hom, NU.dsigup(x, b)) : N.NC(K)}}

def hom(-K: N.Num, -W: POps<K>, R: PLaws<K, W>) -> KH.Hom<KI.dnum(), K>:
  match R:
    case PLaws{hom, l_ofd, l_tod, l_sig, l_round, l_sdiv, l_sigup}:
      hom

def l_ofd(-K: N.Num, -W: POps<K>, R: PLaws<K, W>) -> @x: S.D -> {ofd(K, W, x) == KH.hmap(KI.dnum(), K, hom(K, W, R), x) : N.NC(K)}:
  match R:
    case PLaws{hom, l_ofd, l_tod, l_sig, l_round, l_sdiv, l_sigup}:
      l_ofd

def l_tod(-K: N.Num, -W: POps<K>, R: PLaws<K, W>) -> @x: S.D -> {tod(K, W, KH.hmap(KI.dnum(), K, hom(K, W, R), x)) == x : S.D}:
  match R:
    case PLaws{hom, l_ofd, l_tod, l_sig, l_round, l_sdiv, l_sigup}:
      l_tod

def l_sig(-K: N.Num, -W: POps<K>, R: PLaws<K, W>) -> @x: S.D -> @b: Nat -> {sig(K, W, KH.hmap(KI.dnum(), K, hom(K, W, R), x), b) == KH.hmap(KI.dnum(), K, hom(K, W, R), NU.dsig(x, b)) : N.NC(K)}:
  match R:
    case PLaws{hom, l_ofd, l_tod, l_sig, l_round, l_sdiv, l_sigup}:
      l_sig

def l_round(-K: N.Num, -W: POps<K>, R: PLaws<K, W>) -> @x: S.D -> @p: Nat -> {round(K, W, KH.hmap(KI.dnum(), K, hom(K, W, R), x), p) == KH.hmap(KI.dnum(), K, hom(K, W, R), NU.dround(x, p)) : N.NC(K)}:
  match R:
    case PLaws{hom, l_ofd, l_tod, l_sig, l_round, l_sdiv, l_sigup}:
      l_round

def l_sdiv(-K: N.Num, -W: POps<K>, R: PLaws<K, W>) -> @w: Nat -> @a: S.D -> @b: S.D -> {sdiv(K, W, w, KH.hmap(KI.dnum(), K, hom(K, W, R), a), KH.hmap(KI.dnum(), K, hom(K, W, R), b)) == KH.hmap(KI.dnum(), K, hom(K, W, R), NU.dsdiv(w, a, b)) : N.NC(K)}:
  match R:
    case PLaws{hom, l_ofd, l_tod, l_sig, l_round, l_sdiv, l_sigup}:
      l_sdiv

def l_sigup(-K: N.Num, -W: POps<K>, R: PLaws<K, W>) -> @x: S.D -> @b: Nat -> {sigup(K, W, KH.hmap(KI.dnum(), K, hom(K, W, R), x), b) == KH.hmap(KI.dnum(), K, hom(K, W, R), NU.dsigup(x, b)) : N.NC(K)}:
  match R:
    case PLaws{hom, l_ofd, l_tod, l_sig, l_round, l_sdiv, l_sigup}:
      l_sigup
