import Solutions.SharpCert.Integral

/-!
# Kernel-computed cells for the `SharpCert` checker

Author: rupert-of-salzburg. The checker of `Checker.lean` / `Integral.lean` takes an arbitrary
list of `Cell`s. Here the cells of a uniform q-grid are *computed* (`mkCell`): candidate logs
by range reduction and an atanh series, candidate exps by `expB`, everything rounded to
`2^-48` dyadics. The candidates need no proof; `cellOk` re-checks each of them in the kernel.
So a certificate is only the small `Glob` record, the grid size `K` and the λ-grid `pts`
(generated and pre-checked by `gen_kernel.py`, which mirrors these functions exactly).
-/

namespace DiagRamsey.SharpCert

/-- `⌈v 2^48⌉ / 2^48` and `⌊v 2^48⌋ / 2^48`. -/
def dyU (v : ℚ) : ℚ := (⌈v * 2 ^ 48⌉ : ℚ) / 2 ^ 48
def dyD (v : ℚ) : ℚ := (⌊v * 2 ^ 48⌋ : ℚ) / 2 ^ 48

def candMargin : ℚ := 1 / 2 ^ 40
def ln2Q : ℚ := 6931471805599453094172321 / 10000000000000000000000000

/-- Scale `r` by powers of two into `[2/3, 4/3]`. -/
def redLoop : ℕ → ℚ → ℤ → ℚ × ℤ
  | 0, r, m => (r, m)
  | f + 1, r, m =>
    if 4 / 3 < r then redLoop f (r / 2) (m + 1)
    else if r < 2 / 3 then redLoop f (r * 2) (m - 1)
    else (r, m)

/-- `∑_{k} s^(2k+1)/(2k+1)` with rounding, `pw = s^(2k+1)`. -/
def atanhLoop (s2 : ℚ) : ℕ → ℕ → ℚ → ℚ → ℚ
  | 0, _, _, acc => acc
  | n + 1, k, pw, acc => atanhLoop s2 n (k + 1) (rdn (pw * s2)) (rdn (acc + pw / (2 * k + 1)))

/-- An approximation of `log y` (no correctness claim). -/
def logApprox (y : ℚ) : ℚ :=
  let rm := redLoop 400 y 0
  let s := rdn ((rm.1 - 1) / (rm.1 + 1))
  rm.2 * ln2Q + 2 * atanhLoop (rdn (s * s)) 12 0 s 0

def logHiC (y : ℚ) : ℚ := dyU (logApprox y + candMargin)
def logLoC (y : ℚ) : ℚ := dyD (logApprox y - candMargin)
def expHiC (x : ℚ) : ℚ :=
  match expB fuel (rup x) with
  | some lh => dyU lh.2
  | none => 0
def expLoC (x : ℚ) : ℚ := dyD (expLo x)

def lineVal (a b w M : ℚ) : ℚ := if 0 ≤ M + w then b * (M + w) else a * (M + w)

/-- The candidate cell on `[a, b]`; mirrors `cell_bounds` of `generate.py`. -/
def mkCell (g : Glob) (a b : ℚ) : Cell :=
  let lmA := logHiC (g.mu / a)
  let lmB := logLoC (g.mu / b)
  let l1A := logHiC (1 - a)
  let l1B := logLoC (1 - b)
  let BHi := g.w * lmA
  let BLo := g.w * lmB
  let ALo := (1 - b) / b * (g.lpxLo + g.w * l1B)
  let AHi := (1 - a) / a * (g.lpxHi + g.w * l1A)
  let uHi := expHiC (g.beta * BHi)
  let eLo := expLoC (g.beta * ALo)
  let z := (uHi - g.p * eLo) / (1 - g.p)
  let nb := decide (ALo ≤ BHi)
  let bd := decide (BLo < AHi) && decide (0 < z)
  let y := if bd then (if z ≤ expLo (-4) then -4 else logHiC z) else 0
  let Mb := g.p * AHi + (1 - g.p) / g.beta * y
  let skip := !nb && !bd
  let c :=
    if skip then 0
    else if nb && bd then dyU (max (lineVal a b g.w BHi) (lineVal a b g.w Mb))
    else if nb then dyU (lineVal a b g.w BHi)
    else dyU (lineVal a b g.w Mb)
  { a := a, b := b, lmA := lmA, lmB := lmB, l1A := l1A, l1B := l1B, uHi := uHi, eLo := eLo,
    y := y, c := c, skip := skip }

/-- The uniform grid `q0 + (μ - q0) k / K`. -/
def gridPt (g : Glob) (K k : ℕ) : ℚ := g.q0 + (g.mu - g.q0) * k / K

/-- The `n` consecutive grid cells starting at index `lo`. -/
def gridCells (g : Glob) (K : ℕ) : ℕ → ℕ → List Cell
  | _, 0 => []
  | lo, n + 1 => mkCell g (gridPt g K lo) (gridPt g K (lo + 1)) :: gridCells g K (lo + 1) n

/-- All per-cell checks at once. -/
def cellFull (g : Glob) (pts : List Pt) (c : Cell) : Bool :=
  cellOk g c && pts.all (lineBelow g c)

lemma gridCells_add (g : Glob) (K : ℕ) (m n : ℕ) : ∀ lo,
    gridCells g K lo (m + n) = gridCells g K lo m ++ gridCells g K (lo + m) n := by
  induction m with
  | zero => intro lo; simp [gridCells]
  | succ m ih =>
    intro lo
    rw [show m + 1 + n = (m + n) + 1 by omega]
    simp only [gridCells, ih (lo + 1), List.cons_append]
    rw [show lo + 1 + m = lo + (m + 1) by omega]

lemma chainOk_gridCells (g : Glob) (K : ℕ) (n : ℕ) : ∀ lo,
    chainOk (gridPt g K lo) (gridCells g K lo n) (gridPt g K (lo + n)) = true := by
  induction n with
  | zero => intro lo; simp [gridCells, chainOk]
  | succ n ih =>
    intro lo
    simp only [gridCells, chainOk, mkCell, decide_true, Bool.true_and]
    rw [show lo + (n + 1) = lo + 1 + n by omega]
    exact ih (lo + 1)

lemma all_gridCells_blocks (g : Glob) (K n : ℕ) (f : Cell → Bool) (lo m : ℕ)
    (h : ∀ j < m, (gridCells g K (lo + j * n) n).all f = true) :
    (gridCells g K lo (m * n)).all f = true := by
  induction m with
  | zero => simp [gridCells]
  | succ m ih =>
    rw [show (m + 1) * n = m * n + n by ring, gridCells_add, List.all_append, Bool.and_eq_true]
    exact ⟨ih (fun j hj => h j (by omega)), h m (by omega)⟩

lemma all_gridCells_chunks (g : Glob) (K n : ℕ) (f : Cell → Bool) (m : ℕ)
    (h : ∀ j < m, (gridCells g K (j * n) n).all f = true) :
    (gridCells g K 0 (m * n)).all f = true :=
  all_gridCells_blocks g K n f 0 m (fun j hj => by simpa using h j hj)

theorem cert_neg_of_grid (g : Glob) (K m n : ℕ) (pts : List Pt)
    (hK : K = m * n) (h0 : gridPt g K 0 = g.q0) (hKmu : gridPt g K K = g.mu)
    (hg : g.ok = true) (hch : ∀ j < m, (gridCells g K (j * n) n).all (cellFull g pts) = true)
    {P0 : Pt} {rest : List Pt} (hpts0 : pts = P0 :: rest)
    (hP0 : P0.lam = 0) (hpts : ptsOk (P0 :: rest) = true) (hneg : intUB g (P0 :: rest) < 0) :
    (certFeasible (g.p : ℝ) g.mu g.w g.beta g.x).Nonempty ∧
      cert (g.p : ℝ) g.mu g.w g.beta g.x < 0 := by
  subst hpts0
  have hall := all_gridCells_chunks g K n _ m hch
  rw [← hK] at hall
  have hmem : ∀ c ∈ gridCells g K 0 K, cellFull g (P0 :: rest) c = true :=
    fun c hc => List.all_eq_true.mp hall c hc
  have hchain := chainOk_gridCells g K K 0
  rw [h0, zero_add, hKmu] at hchain
  refine cert_neg_of_checks g (gridCells g K 0 K) P0 rest hg hchain ?_ ?_ hP0 hpts hneg
  · intro c hc
    have := hmem c hc
    simp only [cellFull, Bool.and_eq_true] at this
    exact this.1
  · intro c hc Q hQ
    have := hmem c hc
    simp only [cellFull, Bool.and_eq_true] at this
    exact List.all_eq_true.mp this.2 Q hQ

/-! ## Data-backed cells

The kernel cost of `mkCell` is dominated by computing the candidates. `CellD` carries them as
integers over `2^48` (the generator's exact dyadic values); only `a, b` (from the grid index) and
`skip` are computed. `cellOk` still checks every field. -/

structure CellD where
  k : ℕ
  lmA : ℤ
  lmB : ℤ
  l1A : ℤ
  l1B : ℤ
  uHi : ℤ
  eLo : ℤ
  y : ℤ
  c : ℤ

def dq (n : ℤ) : ℚ := (n : ℚ) / 2 ^ 48

def mkCellD (g : Glob) (K : ℕ) (d : CellD) : Cell :=
  let a := gridPt g K d.k
  let b := gridPt g K (d.k + 1)
  let ALo := (1 - b) / b * (g.lpxLo + g.w * dq d.l1B)
  let AHi := (1 - a) / a * (g.lpxHi + g.w * dq d.l1A)
  let z := (dq d.uHi - g.p * dq d.eLo) / (1 - g.p)
  let nb := decide (ALo ≤ g.w * dq d.lmA)
  let bd := decide (g.w * dq d.lmB < AHi) && decide (0 < z)
  { a := a, b := b, lmA := dq d.lmA, lmB := dq d.lmB, l1A := dq d.l1A, l1B := dq d.l1B,
    uHi := dq d.uHi, eLo := dq d.eLo, y := dq d.y, c := dq d.c, skip := !nb && !bd }

theorem cert_neg_of_data (g : Glob) (K : ℕ) (pts : List Pt) (D : List CellD)
    (hg : g.ok = true) (hch : chainOk g.q0 (D.map (mkCellD g K)) g.mu = true)
    (hall : (D.map (mkCellD g K)).all (cellFull g pts) = true)
    {P0 : Pt} {rest : List Pt} (hpts0 : pts = P0 :: rest)
    (hP0 : P0.lam = 0) (hpts : ptsOk (P0 :: rest) = true) (hneg : intUB g (P0 :: rest) < 0) :
    (certFeasible (g.p : ℝ) g.mu g.w g.beta g.x).Nonempty ∧
      cert (g.p : ℝ) g.mu g.w g.beta g.x < 0 := by
  subst hpts0
  have hmem : ∀ c ∈ D.map (mkCellD g K), cellFull g (P0 :: rest) c = true :=
    fun c hc => List.all_eq_true.mp hall c hc
  refine cert_neg_of_checks g (D.map (mkCellD g K)) P0 rest hg hch ?_ ?_ hP0 hpts hneg
  · intro c hc
    have := hmem c hc
    simp only [cellFull, Bool.and_eq_true] at this
    exact this.1
  · intro c hc Q hQ
    have := hmem c hc
    simp only [cellFull, Bool.and_eq_true] at this
    exact List.all_eq_true.mp this.2 Q hQ

end DiagRamsey.SharpCert
