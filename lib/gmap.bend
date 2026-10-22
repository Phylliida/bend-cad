# bend-cad: numer.bend's results (Maybe values, Newton's states, block and
# plan outcomes) sent entry by entry through a map of computing numbers
# h : KI.dnum() -> K (lib/khom.bend), as lib/gnumer.bend's. Untrusted; the
# statements of lib/gelimpf.bend, lib/gnewtpf.bend and lib/gplanpf.bend use
# them (PLAN-sk13w W4).

import Base
import ../spec/num.bend as S
import ../spec/knum.bend as N
import ./kinst.bend as KI
import ./khom.bend as KH
import ./numer.bend as NU
import ./gnumer.bend as GN

def hmd(~K: N.Num, ~H: KH.Hom<KI.dnum(), K>, m: Maybe<&2, S.D>) -> Maybe<&2, N.NC(K)>:
  match m:
    case None{}:
      None{}
    case Some{x}:
      Some{KH.hmap(KI.dnum(), K, H, x)}

def hmv(~K: N.Num, ~H: KH.Hom<KI.dnum(), K>, m: Maybe<&2, List<&2, S.D>>) -> Maybe<&2, N.KVec(~K)>:
  match m:
    case None{}:
      None{}
    case Some{x}:
      Some{KH.hv(~KI.dnum(), ~K, ~H, x)}

def hmm(~K: N.Num, ~H: KH.Hom<KI.dnum(), K>, m: Maybe<&2, List<&2, List<&2, S.D>>>) -> Maybe<&2, N.KMat(~K)>:
  match m:
    case None{}:
      None{}
    case Some{x}:
      Some{KH.hm(~KI.dnum(), ~K, ~H, x)}

def hns(~K: N.Num, ~H: KH.Hom<KI.dnum(), K>, st: NU.NS) -> GN.GNS<K>:
  match st:
    case NU.NMore{y}:
      GN.GMore{KH.hv(~KI.dnum(), ~K, ~H, y)}
    case NU.NDone{y}:
      GN.GDone{KH.hv(~KI.dnum(), ~K, ~H, y)}
    case NU.NSing{}:
      GN.GSing{}

def hbr(~K: N.Num, ~H: KH.Hom<KI.dnum(), K>, b: NU.BR) -> GN.GBR<K>:
  match b:
    case NU.BOk{c}:
      GN.GBOk{KH.hcert(~KI.dnum(), ~K, ~H, c)}
    case NU.BRetry{}:
      GN.GBRetry{}
    case NU.BStop{}:
      GN.GBStop{}

def hpb(~K: N.Num, ~H: KH.Hom<KI.dnum(), K>, x: NU.PB) -> GN.GPB<K>:
  match x:
    case NU.PB{bs, gc, gr}:
      GN.GPB{KH.hpbs(~KI.dnum(), ~K, ~H, bs), KH.hv(~KI.dnum(), ~K, ~H, gc), KH.hv(~KI.dnum(), ~K, ~H, gr)}

def hpbr(~K: N.Num, ~H: KH.Hom<KI.dnum(), K>, m: NU.PBR) -> GN.GPBR<K>:
  match m:
    case NU.PBOk{pb}:
      GN.GPBOk{hpb(~K, ~H, pb)}
    case NU.PBRetry{}:
      GN.GPBRetry{}
    case NU.PBStop{}:
      GN.GPBStop{}

def hnp(~K: N.Num, ~H: KH.Hom<KI.dnum(), K>, x: NU.NP) -> GN.GNP<K>:
  match x:
    case NU.NP{plan, gc, gr}:
      GN.GNP{KH.hplan(~KI.dnum(), ~K, ~H, plan), KH.hv(~KI.dnum(), ~K, ~H, gc), KH.hv(~KI.dnum(), ~K, ~H, gr)}

def hpr(~K: N.Num, ~H: KH.Hom<KI.dnum(), K>, m: NU.PR) -> GN.GPR<K>:
  match m:
    case NU.POk{np}:
      GN.GPOk{hnp(~K, ~H, np)}
    case NU.PRetry{}:
      GN.GPRetry{}
    case NU.PStop{}:
      GN.GPStop{}
