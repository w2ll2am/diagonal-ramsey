import Solutions.SharpCert.Exp
import Definitions.Def_DiagRamsey_Cert
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Integrability.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# A kernel-checkable certificate format for `cert p μ w β x < 0`

All data is rational. `Cert.ok`-style Boolean checks are evaluated by `decide +kernel`;
`cert_neg_of_checks` turns passing checks into
`(certFeasible p μ w β x).Nonempty ∧ cert p μ w β x < 0`.

Method (see `proofs/DiagRamsey_sharp_cert_1263.md`):
* no `q ≤ q0` is feasible (`Glob.ok`, exclusion inequality);
* `[q0, μ]` is covered by cells `[a, b]` (`chainOk`); on each cell rational log/exp bounds
  bound `A`, `B`, `U`, `e^{βA}` and the binding logarithm, so `q (M q + w) ≤ c` (`cellOk`);
* in `λ = -log t ≥ 0` each feasible `q` gives a value `≤ c - w a λ`; these lines lie below
  `E_j` at grid points `λ_j` (`lineBelow`), hence below the chords; the chords and an
  affine tail are integrated exactly against `dt = e^{-λ} dλ` (`intUB`).
-/

namespace DiagRamsey.SharpCert

open Real Set MeasureTheory

structure Glob where
  p : ℚ
  mu : ℚ
  w : ℚ
  beta : ℚ
  x : ℚ
  q0 : ℚ
  lpxLo : ℚ
  lpxHi : ℚ
  lpinvHi : ℚ
  lmq0Hi : ℚ
  l1q0Lo : ℚ
  l1muLo : ℚ
  l1muHi : ℚ
  wz : ℚ

structure Cell where
  a : ℚ
  b : ℚ
  lmA : ℚ
  lmB : ℚ
  l1A : ℚ
  l1B : ℚ
  uHi : ℚ
  eLo : ℚ
  y : ℚ
  c : ℚ
  skip : Bool

structure Pt where
  lam : ℚ
  E : ℚ
  tLo : ℚ
  tHi : ℚ

def Glob.L0 (g : Glob) : ℚ := g.lpxLo + g.w * g.l1q0Lo

def Glob.ok (g : Glob) : Bool :=
  decide (0 < g.p) && decide (g.p < 1) && decide (0 < g.x) && decide (0 < g.w) &&
  decide (0 < g.beta) && decide (0 < g.q0) && decide (g.q0 < g.mu) && decide (g.mu < 1) &&
  expLeB g.lpxLo (g.p / g.x) && decide (g.p / g.x ≤ expLo g.lpxHi) &&
  decide (1 / g.p ≤ expLo g.lpinvHi) &&
  decide (g.mu / g.q0 ≤ expLo g.lmq0Hi) && expLeB g.l1q0Lo (1 - g.q0) &&
  decide (0 ≤ g.L0 - g.w * g.q0) &&
  decide (0 ≤ (g.L0 - g.w * g.q0) / g.q0 - g.L0 - g.w * g.lmq0Hi + g.w - g.lpinvHi / g.beta) &&
  expLeB g.l1muLo (1 - g.mu) && decide (1 - g.mu ≤ expLo g.l1muHi) &&
  decide (0 < (1 - g.mu) / g.mu * (g.lpxLo + g.w * g.l1muLo)) &&
  expLeB (g.beta * ((1 - g.mu) / g.mu * (g.lpxHi + g.w * g.l1muHi))) g.wz &&
  decide (g.p * g.wz < 1)

section cell
variable (g : Glob) (c : Cell)
def Cell.BHi : ℚ := g.w * c.lmA
def Cell.BLo : ℚ := g.w * c.lmB
def Cell.LLo : ℚ := g.lpxLo + g.w * c.l1B
def Cell.LHi : ℚ := g.lpxHi + g.w * c.l1A
def Cell.ALo : ℚ := (1 - c.b) / c.b * c.LLo g
def Cell.AHi : ℚ := (1 - c.a) / c.a * c.LHi g
def Cell.z : ℚ := (c.uHi - g.p * c.eLo) / (1 - g.p)
def Cell.nbPos : Bool := decide (c.ALo g ≤ c.BHi g)
def Cell.bdPos : Bool := decide (c.BLo g < c.AHi g) && decide (0 < c.z g)
def Cell.Mb : ℚ := g.p * c.AHi g + (1 - g.p) / g.beta * c.y
def Cell.lineOk (M : ℚ) : Bool :=
  if 0 ≤ M + g.w then decide (c.b * (M + g.w) ≤ c.c) else decide (c.a * (M + g.w) ≤ c.c)

def cellOk : Bool :=
  decide (c.a < c.b) && decide (g.q0 ≤ c.a) && decide (c.b ≤ g.mu) &&
  decide (g.mu / c.a ≤ expLo c.lmA) && expLeB c.lmB (g.mu / c.b) &&
  decide (1 - c.a ≤ expLo c.l1A) && expLeB c.l1B (1 - c.b) &&
  decide (0 ≤ c.LLo g) &&
  expLeB (g.beta * c.BHi g) c.uHi && decide (c.eLo ≤ expLo (g.beta * c.ALo g)) &&
  (!c.bdPos g || decide (c.z g ≤ expLo c.y)) &&
  (if c.skip then !c.nbPos g && !c.bdPos g
   else (!c.nbPos g || c.lineOk g (c.BHi g)) && (!c.bdPos g || c.lineOk g (c.Mb g)))

def lineBelow (pt : Pt) : Bool := c.skip || decide (c.c - g.w * c.a * pt.lam ≤ pt.E)
end cell

def chainOk : ℚ → List Cell → ℚ → Bool
  | lo, [], hi => decide (lo = hi)
  | lo, c :: cs, hi => decide (c.a = lo) && chainOk c.b cs hi

def ptOk (pt : Pt) : Bool := decide (pt.tLo ≤ expLo (-pt.lam)) && expLeB (-pt.lam) pt.tHi

def ptsOk : List Pt → Bool
  | [] => true
  | [P] => ptOk P
  | P0 :: P1 :: rest => ptOk P0 && decide (P0.lam < P1.lam) && ptsOk (P1 :: rest)

def mulUB (lo hi c : ℚ) : ℚ := if 0 ≤ c then hi * c else lo * c

def segUB (P0 P1 : Pt) : ℚ :=
  mulUB P0.tLo P0.tHi (P0.E + (P1.E - P0.E) / (P1.lam - P0.lam)) +
    mulUB P1.tLo P1.tHi (-(P1.E + (P1.E - P0.E) / (P1.lam - P0.lam)))

def tailUB (g : Glob) (P : Pt) : ℚ := mulUB P.tLo P.tHi (P.E - g.w * g.q0)

def intUB (g : Glob) : List Pt → ℚ
  | [] => 0
  | [P] => tailUB g P
  | P0 :: P1 :: rest => segUB P0 P1 + intUB g (P1 :: rest)

/-! ## Soundness -/

lemma mulUB_spec {lo hi c : ℚ} {t : ℝ} (hlo : (lo : ℝ) ≤ t) (hhi : t ≤ hi) :
    t * c ≤ (mulUB lo hi c : ℝ) := by
  unfold mulUB
  split_ifs with h
  · have : (0 : ℝ) ≤ c := by exact_mod_cast h
    push_cast; nlinarith
  · have : (c : ℝ) < 0 := by exact_mod_cast (not_le.mp h)
    push_cast; nlinarith

/-- Real-number facts extracted from `Glob.ok`. -/
structure GlobFacts (g : Glob) : Prop where
  p0 : (0 : ℝ) < g.p
  p1 : (g.p : ℝ) < 1
  x0 : (0 : ℝ) < g.x
  w0 : (0 : ℝ) < g.w
  b0 : (0 : ℝ) < g.beta
  q00 : (0 : ℝ) < g.q0
  q0mu : (g.q0 : ℝ) < g.mu
  mu1 : (g.mu : ℝ) < 1
  lpxLo : (g.lpxLo : ℝ) ≤ Real.log (g.p / g.x)
  lpxHi : Real.log (g.p / g.x) ≤ g.lpxHi
  lpinv : Real.log (1 / g.p) ≤ g.lpinvHi
  lmq0 : Real.log (g.mu / g.q0) ≤ g.lmq0Hi
  l1q0 : (g.l1q0Lo : ℝ) ≤ Real.log (1 - g.q0)
  K1 : (0 : ℝ) ≤ (g.lpxLo + g.w * g.l1q0Lo) - g.w * g.q0
  K2 : (0 : ℝ) ≤ ((g.lpxLo + g.w * g.l1q0Lo) - g.w * g.q0) / g.q0 - (g.lpxLo + g.w * g.l1q0Lo)
      - g.w * g.lmq0Hi + g.w - g.lpinvHi / g.beta
  l1muLo : (g.l1muLo : ℝ) ≤ Real.log (1 - g.mu)
  l1muHi : Real.log (1 - g.mu) ≤ g.l1muHi
  amu : (0 : ℝ) < (1 - g.mu) / g.mu * (g.lpxLo + g.w * g.l1muLo)
  wz : Real.exp (g.beta * ((1 - g.mu) / g.mu * (g.lpxHi + g.w * g.l1muHi))) ≤ g.wz
  pwz : (g.p : ℝ) * g.wz < 1

lemma Glob.facts {g : Glob} (h : g.ok = true) : GlobFacts g := by
  simp only [Glob.ok, Glob.L0, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hp0, hp1⟩, hx0⟩, hw0⟩, hb0⟩, hq00⟩, hq0mu⟩, hmu1⟩, hlpxLo⟩, hlpxHi⟩,
    hlpinv⟩, hlmq0⟩, hl1q0⟩, hK1⟩, hK2⟩, hl1muLo⟩, hl1muHi⟩, hamu⟩, hwz⟩, hpwz⟩ := h
  have hp0' : (0 : ℚ) < g.p / g.x := div_pos hp0 hx0
  refine
    { p0 := by exact_mod_cast hp0
      p1 := by exact_mod_cast hp1
      x0 := by exact_mod_cast hx0
      w0 := by exact_mod_cast hw0
      b0 := by exact_mod_cast hb0
      q00 := by exact_mod_cast hq00
      q0mu := by exact_mod_cast hq0mu
      mu1 := by exact_mod_cast hmu1
      lpxLo := ?_, lpxHi := ?_, lpinv := ?_, lmq0 := ?_, l1q0 := ?_
      K1 := by exact_mod_cast hK1
      K2 := by exact_mod_cast hK2
      l1muLo := ?_, l1muHi := ?_
      amu := by exact_mod_cast hamu
      wz := by exact_mod_cast exp_le_of_expLeB hwz
      pwz := by exact_mod_cast hpwz }
  · have := le_log_of_expLeB hp0' hlpxLo; push_cast at this; exact this
  · have := log_le_of_le_expLo hp0' hlpxHi; push_cast at this; exact this
  · have := log_le_of_le_expLo (by positivity) hlpinv; push_cast at this; exact this
  · have := log_le_of_le_expLo (div_pos (hq00.trans hq0mu) hq00) hlmq0; push_cast at this
    exact this
  · have := le_log_of_expLeB (by linarith) hl1q0; push_cast at this; exact this
  · have := le_log_of_expLeB (by linarith) hl1muLo; push_cast at this; exact this
  · have := log_le_of_le_expLo (by linarith) hl1muHi; push_cast at this; exact this

section real
variable {p μ w β x : ℝ}

lemma certA_eq {q : ℝ} (hp : 0 < p) (hx : 0 < x) (hq1 : q < 1) :
    certA p w x q = (1 - q) / q * (Real.log (p / x) + w * Real.log (1 - q)) := by
  unfold certA
  have h1 : (0 : ℝ) < 1 - q := by linarith
  rw [mul_div_right_comm, Real.log_mul (by positivity) (by positivity), Real.log_rpow h1]

lemma feasible_lt {q : ℝ} (hp : 0 < p) (hp1 : p < 1) (hβ : 0 < β)
    (hq : q ∈ certFeasible p μ w β x) :
    certA p w x q < certB μ w q + Real.log (1 / p) / β := by
  have hlp : 0 < Real.log (1 / p) := Real.log_pos (by rw [lt_div_iff₀ hp]; linarith)
  rcases hq.2.2 with h | ⟨-, h⟩
  · have : 0 < Real.log (1 / p) / β := div_pos hlp hβ
    linarith
  · unfold certU at h
    have h2 := Real.log_lt_log (by positivity) h
    rw [Real.log_mul hp.ne' (Real.exp_pos _).ne', Real.log_exp, Real.log_exp] at h2
    rw [one_div, Real.log_inv, ← sub_pos]
    have e : certB μ w q + -Real.log p / β - certA p w x q =
        (β * certB μ w q - Real.log p - β * certA p w x q) / β := by
      field_simp; ring
    rw [e]; exact div_pos (by linarith) hβ

end real

lemma excl {g : Glob} (hg : GlobFacts g) {q : ℝ}
    (hq : q ∈ certFeasible g.p g.mu g.w g.beta g.x) : (g.q0 : ℝ) < q := by
  by_contra hle
  push Not at hle
  have hq0 := hq.1
  have hqmu := hq.2.1
  have hlt := feasible_lt hg.p0 hg.p1 hg.b0 hq
  have hq1 : q < 1 := by linarith [hg.mu1]
  rw [certA_eq hg.p0 hg.x0 hq1] at hlt
  unfold certB at hlt
  have hlog1 : Real.log (1 - g.q0) ≤ Real.log (1 - q) :=
    Real.log_le_log (by linarith [hg.q0mu, hg.mu1]) (by linarith)
  set L0 : ℝ := g.lpxLo + g.w * g.l1q0Lo with hL0
  have hL : L0 ≤ Real.log (g.p / g.x) + g.w * Real.log (1 - q) := by
    have := hg.lpxLo; have := hg.l1q0; have := hg.w0
    nlinarith
  have hu : (1 - q) / q = 1 / q - 1 := by field_simp
  have hu0 : (1 : ℝ) / g.q0 ≤ 1 / q := one_div_le_one_div_of_le hq0 hle
  have hu1 : 1 ≤ 1 / q := by
    rw [le_div_iff₀ hq0]; linarith
  have hK1 := hg.K1
  have hA : (1 / q - 1) * L0 ≤ (1 - q) / q * (Real.log (g.p / g.x) + g.w * Real.log (1 - q)) := by
    rw [hu]; exact mul_le_mul_of_nonneg_left hL (by linarith)
  have hB : Real.log (g.mu / q) ≤ g.lmq0Hi + (g.q0 * (1 / q) - 1) := by
    have hm : (g.mu : ℝ) / q = (g.mu / g.q0) * (g.q0 / q) := by
      field_simp [hg.q00.ne', hq0.ne']
    have hpos : (0 : ℝ) < g.q0 / q := div_pos hg.q00 hq0
    rw [hm, Real.log_mul (div_pos (hg.q00.trans hg.q0mu) hg.q00).ne' hpos.ne']
    have := Real.log_le_sub_one_of_pos hpos
    have := hg.lmq0
    rw [mul_one_div]; linarith
  have hc : Real.log (1 / g.p) / g.beta ≤ g.lpinvHi / g.beta :=
    div_le_div_of_nonneg_right hg.lpinv hg.b0.le
  have hK2 := hg.K2
  rw [← hL0] at hK2
  have hlin : (1 / q - 1 / g.q0) * (L0 - g.w * g.q0) ≥ 0 :=
    mul_nonneg (by linarith) hK1
  have hq0inv : (g.q0 : ℝ) * (1 / g.q0) = 1 := by field_simp [hg.q00.ne']
  have hw := hg.w0
  have : (L0 - g.w * g.q0) / g.q0 = (1 / g.q0) * (L0 - g.w * g.q0) := by ring
  rw [this] at hK2
  nlinarith [mul_le_mul_of_nonneg_left hB hw.le]

lemma witness {g : Glob} (hg : GlobFacts g) :
    (g.mu : ℝ) ∈ certFeasible g.p g.mu g.w g.beta g.x ∧
      0 < certA g.p g.w g.x g.mu := by
  have hmu0 : (0 : ℝ) < g.mu := hg.q00.trans hg.q0mu
  have hmu1 := hg.mu1
  have hB : certB (g.mu : ℝ) g.w g.mu = 0 := by simp [certB, div_self hmu0.ne']
  have hA := certA_eq (w := (g.w : ℝ)) hg.p0 hg.x0 hmu1
  have hfac : (0 : ℝ) < (1 - g.mu) / g.mu := div_pos (by linarith) hmu0
  have hAlo : (1 - (g.mu : ℝ)) / g.mu * (g.lpxLo + g.w * g.l1muLo) ≤ certA g.p g.w g.x g.mu := by
    rw [hA]
    apply mul_le_mul_of_nonneg_left _ hfac.le
    have := hg.lpxLo; have := hg.l1muLo; have := hg.w0; nlinarith
  have hAhi : certA (g.p : ℝ) g.w g.x g.mu ≤ (1 - g.mu) / g.mu * (g.lpxHi + g.w * g.l1muHi) := by
    rw [hA]
    apply mul_le_mul_of_nonneg_left _ hfac.le
    have := hg.lpxHi; have := hg.l1muHi; have := hg.w0; nlinarith
  have hApos : 0 < certA (g.p : ℝ) g.w g.x g.mu := lt_of_lt_of_le hg.amu hAlo
  refine ⟨⟨hmu0, le_rfl, Or.inr ⟨by rw [hB]; exact hApos, ?_⟩⟩, hApos⟩
  unfold certU; rw [hB, mul_zero, Real.exp_zero]
  have h1 : Real.exp (g.beta * certA (g.p : ℝ) g.w g.x g.mu) ≤ g.wz :=
    (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hAhi hg.b0.le)).trans hg.wz
  have := hg.pwz
  nlinarith [hg.p0]

lemma lineOk_spec {g : Glob} {c : Cell} {Mh : ℚ} {m q : ℝ}
    (hM : m ≤ Mh) (ha : (c.a : ℝ) ≤ q) (hb : q ≤ c.b) (ha0 : (0 : ℝ) < c.a)
    (hl : c.lineOk g Mh = true) : q * (m + g.w) ≤ c.c := by
  unfold Cell.lineOk at hl
  split_ifs at hl with h
  · have h' : (0 : ℝ) ≤ Mh + g.w := by exact_mod_cast h
    have hl' : ((c.b : ℝ)) * (Mh + g.w) ≤ c.c := by exact_mod_cast of_decide_eq_true hl
    nlinarith
  · have h' : (Mh : ℝ) + g.w < 0 := by exact_mod_cast (not_le.mp h)
    have hl' : ((c.a : ℝ)) * (Mh + g.w) ≤ c.c := by exact_mod_cast of_decide_eq_true hl
    nlinarith

lemma cell_spec {g : Glob} {c : Cell} (hg : GlobFacts g) (hc : cellOk g c = true) {q : ℝ}
    (ha : (c.a : ℝ) ≤ q) (hb : q ≤ c.b) (hq : q ∈ certFeasible g.p g.mu g.w g.beta g.x) :
    c.skip = false ∧ q * (certM g.p g.mu g.w g.beta g.x q + g.w) ≤ c.c := by
  simp only [cellOk, Bool.and_eq_true, decide_eq_true_eq] at hc
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hab, hq0a⟩, hbmu⟩, hlmA⟩, hlmB⟩, hl1A⟩, hl1B⟩, hLLo⟩, huHi⟩, heLo⟩, hy⟩,
    hcase⟩ := hc
  have ha0 : (0 : ℝ) < c.a := lt_of_lt_of_le hg.q00 (by exact_mod_cast hq0a)
  have hq0 : 0 < q := ha0.trans_le ha
  have hb' : (c.b : ℝ) ≤ g.mu := by exact_mod_cast hbmu
  have hmu1 := hg.mu1
  have hq1 : q < 1 := by linarith [hg.mu1]
  have hmu0 : (0 : ℝ) < g.mu := hg.q00.trans hg.q0mu
  have hb0 : (0 : ℝ) < c.b := hq0.trans_le hb
  have hw := hg.w0
  -- logarithm bounds
  have hlmA' : Real.log (g.mu / c.a) ≤ c.lmA := by
    have := log_le_of_le_expLo (div_pos (by exact_mod_cast hmu0) (by exact_mod_cast ha0)) hlmA
    push_cast at this; exact this
  have hlmB' : (c.lmB : ℝ) ≤ Real.log (g.mu / c.b) := by
    have := le_log_of_expLeB (div_pos (by exact_mod_cast hmu0) (by exact_mod_cast hb0)) hlmB
    push_cast at this; exact this
  have hl1A' : Real.log (1 - c.a) ≤ c.l1A := by
    have := log_le_of_le_expLo (by have : (c.a : ℝ) < 1 := by linarith
                                   exact_mod_cast (sub_pos.mpr this)) hl1A
    push_cast at this; exact this
  have hl1B' : (c.l1B : ℝ) ≤ Real.log (1 - c.b) := by
    have := le_log_of_expLeB (by have : (c.b : ℝ) < 1 := by linarith
                                 exact_mod_cast (sub_pos.mpr this)) hl1B
    push_cast at this; exact this
  -- B bounds
  have hBq : certB (g.mu : ℝ) g.w q = g.w * Real.log (g.mu / q) := rfl
  have hBhi : certB (g.mu : ℝ) g.w q ≤ c.BHi g := by
    rw [hBq, Cell.BHi]; push_cast
    apply mul_le_mul_of_nonneg_left _ hw.le
    refine le_trans (Real.log_le_log (div_pos hmu0 hq0) ?_) hlmA'
    exact div_le_div_of_nonneg_left hmu0.le ha0 ha
  have hBlo : (c.BLo g : ℝ) ≤ certB (g.mu : ℝ) g.w q := by
    rw [hBq, Cell.BLo]; push_cast
    apply mul_le_mul_of_nonneg_left _ hw.le
    refine hlmB'.trans (Real.log_le_log (div_pos hmu0 hb0) ?_)
    exact div_le_div_of_nonneg_left hmu0.le hq0 hb
  -- A bounds
  have hA := certA_eq (w := (g.w : ℝ)) hg.p0 hg.x0 hq1
  have hl1q : Real.log (1 - q) ≤ Real.log (1 - c.a) := Real.log_le_log (by linarith) (by linarith)
  have hl1q' : Real.log (1 - c.b) ≤ Real.log (1 - q) := Real.log_le_log (by linarith) (by linarith)
  have hLlo : (c.LLo g : ℝ) ≤ Real.log (g.p / g.x) + g.w * Real.log (1 - q) := by
    rw [Cell.LLo]; push_cast; have := hg.lpxLo; nlinarith
  have hLhi : Real.log (g.p / g.x) + g.w * Real.log (1 - q) ≤ c.LHi g := by
    rw [Cell.LHi]; push_cast; have := hg.lpxHi; nlinarith
  have hLLo' : (0 : ℝ) ≤ c.LLo g := by exact_mod_cast hLLo
  have hf1 : (1 - (c.b : ℝ)) / c.b ≤ (1 - q) / q := by
    rw [sub_div, sub_div, div_self hb0.ne', div_self hq0.ne']
    linarith [one_div_le_one_div_of_le hq0 hb]
  have hf2 : (1 - q) / q ≤ (1 - (c.a : ℝ)) / c.a := by
    rw [sub_div, sub_div, div_self ha0.ne', div_self hq0.ne']
    linarith [one_div_le_one_div_of_le ha0 ha]
  have hf0 : (0 : ℝ) ≤ (1 - c.b) / c.b := div_nonneg (by linarith) hb0.le
  have hAlo : (c.ALo g : ℝ) ≤ certA (g.p : ℝ) g.w g.x q := by
    rw [hA, Cell.ALo]; push_cast
    exact mul_le_mul hf1 hLlo hLLo' (hf0.trans hf1)
  have hAhi : certA (g.p : ℝ) g.w g.x q ≤ c.AHi g := by
    rw [hA, Cell.AHi]; push_cast
    exact mul_le_mul hf2 hLhi (hLLo'.trans hLlo) (hf0.trans (hf1.trans hf2))
  rcases hq.2.2 with hnb | ⟨hBA, hbind⟩
  · -- non-binding
    have hnbP : c.nbPos g = true := by
      simp only [Cell.nbPos, decide_eq_true_eq]
      exact_mod_cast hAlo.trans (hnb.trans hBhi)
    have hM : certM (g.p : ℝ) g.mu g.w g.beta g.x q = certB (g.mu : ℝ) g.w q := by
      simp [certM, hnb]
    cases hs : c.skip
    · rw [hs] at hcase
      simp only [hnbP, Bool.not_true, Bool.false_or, Bool.false_eq_true, ↓reduceIte,
        Bool.and_eq_true] at hcase
      refine ⟨rfl, ?_⟩
      rw [hM]; exact lineOk_spec hBhi ha hb ha0 hcase.1
    · rw [hs] at hcase; simp [hnbP] at hcase
  · -- binding
    have hU1 := exp_le_of_expLeB huHi
    push_cast at hU1
    have hU : certU (g.mu : ℝ) g.w g.beta q ≤ c.uHi :=
      (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hBhi hg.b0.le)).trans hU1
    have hE1 : (c.eLo : ℝ) ≤ expLo (g.beta * c.ALo g) := by exact_mod_cast heLo
    have hE2 := expLo_le (g.beta * c.ALo g)
    push_cast at hE2
    have hE : (c.eLo : ℝ) ≤ Real.exp (g.beta * certA (g.p : ℝ) g.w g.x q) :=
      hE1.trans (hE2.trans (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hAlo hg.b0.le)))
    have hp1 : (0 : ℝ) < 1 - g.p := by linarith [hg.p1]
    set zr := (certU (g.mu : ℝ) g.w g.beta q - g.p * Real.exp (g.beta * certA (g.p : ℝ) g.w g.x q))
      / (1 - g.p) with hzr
    have hzr0 : 0 < zr := div_pos (by linarith) hp1
    have hzz : zr ≤ c.z g := by
      rw [Cell.z]; push_cast
      apply div_le_div_of_nonneg_right _ hp1.le
      nlinarith [hg.p0]
    have hbdP : c.bdPos g = true := by
      simp only [Cell.bdPos, Bool.and_eq_true, decide_eq_true_eq]
      constructor
      · exact_mod_cast hBlo.trans_lt (hBA.trans_le hAhi)
      · exact_mod_cast hzr0.trans_le hzz
    rw [hbdP] at hy
    simp only [Bool.not_true, Bool.false_or, decide_eq_true_eq] at hy
    have hlogz : Real.log zr ≤ c.y := by
      have := log_le_of_le_expLo (by exact_mod_cast hzr0.trans_le hzz) hy
      exact (Real.log_le_log hzr0 hzz).trans this
    have hM : certM (g.p : ℝ) g.mu g.w g.beta g.x q ≤ c.Mb g := by
      rw [certM, if_neg (not_le.mpr hBA), Cell.Mb]; push_cast
      have h1 : (g.p : ℝ) * certA g.p g.w g.x q ≤ g.p * c.AHi g :=
        mul_le_mul_of_nonneg_left hAhi hg.p0.le
      have h2 : (1 - (g.p : ℝ)) / g.beta * Real.log zr ≤ (1 - g.p) / g.beta * c.y :=
        mul_le_mul_of_nonneg_left hlogz (div_nonneg hp1.le hg.b0.le)
      rw [← hzr]; linarith
    cases hs : c.skip
    · rw [hs] at hcase
      simp only [hbdP, Bool.not_true, Bool.false_or, Bool.false_eq_true, ↓reduceIte,
        Bool.and_eq_true] at hcase
      exact ⟨rfl, lineOk_spec hM ha hb ha0 hcase.2⟩
    · rw [hs] at hcase; simp [hbdP] at hcase

lemma chain_mem : ∀ (cs : List Cell) (lo hi : ℚ), chainOk lo cs hi = true →
    ∀ q : ℝ, (lo : ℝ) < q → q ≤ hi → ∃ c ∈ cs, (c.a : ℝ) ≤ q ∧ q ≤ c.b := by
  intro cs
  induction cs with
  | nil =>
    intro lo hi h q h1 h2
    simp only [chainOk, decide_eq_true_eq] at h
    subst h; linarith
  | cons c cs ih =>
    intro lo hi h q h1 h2
    simp only [chainOk, Bool.and_eq_true, decide_eq_true_eq] at h
    by_cases hq : q ≤ c.b
    · exact ⟨c, List.mem_cons_self .., by rw [h.1]; exact h1.le, hq⟩
    · obtain ⟨c', hc', h'⟩ := ih _ _ h.2 q (not_le.mp hq) h2
      exact ⟨c', List.mem_cons_of_mem _ hc', h'⟩

end DiagRamsey.SharpCert
