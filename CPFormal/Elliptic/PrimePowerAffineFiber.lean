import CPFormal.Elliptic.PrimePowerReductionFiber

/-!
# Intrinsic affine prime-power fibers

This file upgrades the coordinate digit decomposition to the displayed affine
short-Weierstrass state tower.  A raw Taylor increment fiber above integral
representatives `(x,y)` is mapped to the actual `MapFiber` of reduction from
`p^(k+1)` to `p^k`.  The map is bijective, so the raw coordinate description is
intrinsic.  Composing two such equivalences proves independence from the chosen
integral representatives of the same target state.
-/

set_option autoImplicit false

namespace CPFormal.Elliptic

noncomputable section

/-- The coordinate lift is injective in its digit. -/
theorem primePowerCoordinateLift_injective
    (p k : ℕ) [NeZero p] (x : ℤ) :
    Function.Injective (primePowerCoordinateLift p k x) := by
  intro u v huv
  apply primePowerCoordinateFiberMap_injective p k x
  apply Subtype.ext
  exact huv

/-- The affine-plane point determined by one certified raw increment pair. -/
def rawWeierstrassLiftPoint
    (p k : ℕ) (a b x y : ℤ)
    (uv : RawWeierstrassLiftFiber p k a b x y) :
    ZMod (p ^ (k + 1)) × ZMod (p ^ (k + 1)) :=
  (primePowerCoordinateLift p k x uv.1.1,
    primePowerCoordinateLift p k y uv.1.2)

@[simp]
theorem rawWeierstrassLiftPoint_fst
    (p k : ℕ) (a b x y : ℤ)
    (uv : RawWeierstrassLiftFiber p k a b x y) :
    (rawWeierstrassLiftPoint p k a b x y uv).1 =
      primePowerCoordinateLift p k x uv.1.1 :=
  rfl

@[simp]
theorem rawWeierstrassLiftPoint_snd
    (p k : ℕ) (a b x y : ℤ)
    (uv : RawWeierstrassLiftFiber p k a b x y) :
    (rawWeierstrassLiftPoint p k a b x y uv).2 =
      primePowerCoordinateLift p k y uv.1.2 :=
  rfl

/-- The raw affine-plane point satisfies the displayed equation. -/
theorem rawWeierstrassLiftPoint_mem
    (p k : ℕ) [Fact (Nat.Prime p)]
    (a b x y : ℤ)
    (uv : RawWeierstrassLiftFiber p k a b x y) :
    shortWeierstrassResidual a b
      (rawWeierstrassLiftPoint p k a b x y uv) = 0 := by
  have hdiv :
      (((p ^ (k + 1) : ℕ) : ℤ) ∣
        shortWeierstrassResidualInt a b
          (x + (p : ℤ) ^ k * (ZMod.cast uv.1.1 : ℤ))
          (y + (p : ℤ) ^ k * (ZMod.cast uv.1.2 : ℤ))) := by
    simpa only [Nat.cast_pow] using uv.2
  have hz :
      (shortWeierstrassResidualInt a b
          (x + (p : ℤ) ^ k * (ZMod.cast uv.1.1 : ℤ))
          (y + (p : ℤ) ^ k * (ZMod.cast uv.1.2 : ℤ)) :
        ZMod (p ^ (k + 1))) = 0 :=
    (CharP.intCast_eq_zero_iff
      (ZMod (p ^ (k + 1))) (p ^ (k + 1)) _).2 hdiv
  change
    shortWeierstrassResidual a b
      (((x + (p : ℤ) ^ k * (ZMod.cast uv.1.1 : ℤ) : ℤ) :
          ZMod (p ^ (k + 1))),
        ((y + (p : ℤ) ^ k * (ZMod.cast uv.1.2 : ℤ) : ℤ) :
          ZMod (p ^ (k + 1)))) = 0
  rw [shortWeierstrassResidual_intCast]
  exact hz

/-- The affine source state determined by a certified raw increment pair. -/
def rawWeierstrassLiftSourceState
    (p k : ℕ) [Fact (Nat.Prime p)]
    (a b x y : ℤ)
    (uv : RawWeierstrassLiftFiber p k a b x y) :
    AffineCongruenceState (p ^ (k + 1)) a b :=
  ⟨rawWeierstrassLiftPoint p k a b x y uv,
    rawWeierstrassLiftPoint_mem p k a b x y uv⟩

@[simp]
theorem rawWeierstrassLiftSourceState_fst
    (p k : ℕ) [Fact (Nat.Prime p)]
    (a b x y : ℤ)
    (uv : RawWeierstrassLiftFiber p k a b x y) :
    (rawWeierstrassLiftSourceState p k a b x y uv).1.1 =
      primePowerCoordinateLift p k x uv.1.1 :=
  rfl

@[simp]
theorem rawWeierstrassLiftSourceState_snd
    (p k : ℕ) [Fact (Nat.Prime p)]
    (a b x y : ℤ)
    (uv : RawWeierstrassLiftFiber p k a b x y) :
    (rawWeierstrassLiftSourceState p k a b x y uv).1.2 =
      primePowerCoordinateLift p k y uv.1.2 :=
  rfl

/--
A raw Taylor increment produces an actual point in the intrinsic reduction
fiber above any target represented by `(x,y)` modulo `p^k`.
-/
def rawWeierstrassLiftFiberMap
    (p k : ℕ) [Fact (Nat.Prime p)]
    (a b x y : ℤ)
    (target : AffineCongruenceState (p ^ k) a b)
    (hx : (x : ZMod (p ^ k)) = target.1.1)
    (hy : (y : ZMod (p ^ k)) = target.1.2) :
    RawWeierstrassLiftFiber p k a b x y →
      MapFiber
        (affineCongruenceStateReduction
          (primePowerStepDvd p k) a b)
        target := by
  letI : NeZero p := ⟨(Fact.out : Nat.Prime p).ne_zero⟩
  intro uv
  refine ⟨rawWeierstrassLiftSourceState p k a b x y uv, ?_⟩
  apply Subtype.ext
  apply Prod.ext
  · simpa [affineCongruenceStateReduction, zmodPointReduction] using
      (zmodReduction_primePowerCoordinateLift p k x uv.1.1).trans hx
  · simpa [affineCongruenceStateReduction, zmodPointReduction] using
      (zmodReduction_primePowerCoordinateLift p k y uv.1.2).trans hy

@[simp]
theorem rawWeierstrassLiftFiberMap_source_fst
    (p k : ℕ) [Fact (Nat.Prime p)]
    (a b x y : ℤ)
    (target : AffineCongruenceState (p ^ k) a b)
    (hx : (x : ZMod (p ^ k)) = target.1.1)
    (hy : (y : ZMod (p ^ k)) = target.1.2)
    (uv : RawWeierstrassLiftFiber p k a b x y) :
    (rawWeierstrassLiftFiberMap
      p k a b x y target hx hy uv).1.1.1 =
      primePowerCoordinateLift p k x uv.1.1 := by
  change
    (rawWeierstrassLiftSourceState p k a b x y uv).1.1 =
      primePowerCoordinateLift p k x uv.1.1
  rfl

@[simp]
theorem rawWeierstrassLiftFiberMap_source_snd
    (p k : ℕ) [Fact (Nat.Prime p)]
    (a b x y : ℤ)
    (target : AffineCongruenceState (p ^ k) a b)
    (hx : (x : ZMod (p ^ k)) = target.1.1)
    (hy : (y : ZMod (p ^ k)) = target.1.2)
    (uv : RawWeierstrassLiftFiber p k a b x y) :
    (rawWeierstrassLiftFiberMap
      p k a b x y target hx hy uv).1.1.2 =
      primePowerCoordinateLift p k y uv.1.2 := by
  change
    (rawWeierstrassLiftSourceState p k a b x y uv).1.2 =
      primePowerCoordinateLift p k y uv.1.2
  rfl

/-- The raw-to-intrinsic affine fiber map is injective. -/
theorem rawWeierstrassLiftFiberMap_injective
    (p k : ℕ) [Fact (Nat.Prime p)]
    (a b x y : ℤ)
    (target : AffineCongruenceState (p ^ k) a b)
    (hx : (x : ZMod (p ^ k)) = target.1.1)
    (hy : (y : ZMod (p ^ k)) = target.1.2) :
    Function.Injective
      (rawWeierstrassLiftFiberMap p k a b x y target hx hy) := by
  letI : NeZero p := ⟨(Fact.out : Nat.Prime p).ne_zero⟩
  intro u v huv
  apply Subtype.ext
  apply Prod.ext
  · apply primePowerCoordinateLift_injective p k x
    have hcoord := congrArg (fun q => q.1.1.1) huv
    simpa only [rawWeierstrassLiftFiberMap_source_fst] using hcoord
  · apply primePowerCoordinateLift_injective p k y
    have hcoord := congrArg (fun q => q.1.1.2) huv
    simpa only [rawWeierstrassLiftFiberMap_source_snd] using hcoord

/-- Every intrinsic affine reduction-fiber point has unique raw digits. -/
theorem rawWeierstrassLiftFiberMap_surjective
    (p k : ℕ) [Fact (Nat.Prime p)]
    (a b x y : ℤ)
    (target : AffineCongruenceState (p ^ k) a b)
    (hx : (x : ZMod (p ^ k)) = target.1.1)
    (hy : (y : ZMod (p ^ k)) = target.1.2) :
    Function.Surjective
      (rawWeierstrassLiftFiberMap p k a b x y target hx hy) := by
  letI : NeZero p := ⟨(Fact.out : Nat.Prime p).ne_zero⟩
  intro point
  let xFiber :
      MapFiber
        (zmodReduction (primePowerStepDvd p k))
        (x : ZMod (p ^ k)) :=
    ⟨point.1.1.1, by
      calc
        zmodReduction (primePowerStepDvd p k) point.1.1.1 =
            target.1.1 := by
          simpa [affineCongruenceStateReduction, zmodPointReduction] using
            congrArg
              (fun state : AffineCongruenceState (p ^ k) a b => state.1.1)
              point.2
        _ = (x : ZMod (p ^ k)) := hx.symm⟩
  let yFiber :
      MapFiber
        (zmodReduction (primePowerStepDvd p k))
        (y : ZMod (p ^ k)) :=
    ⟨point.1.1.2, by
      calc
        zmodReduction (primePowerStepDvd p k) point.1.1.2 =
            target.1.2 := by
          simpa [affineCongruenceStateReduction, zmodPointReduction] using
            congrArg
              (fun state : AffineCongruenceState (p ^ k) a b => state.1.2)
              point.2
        _ = (y : ZMod (p ^ k)) := hy.symm⟩
  let u : ZMod p :=
    (primePowerCoordinateReductionFiberEquiv p k x).symm xFiber
  let v : ZMod p :=
    (primePowerCoordinateReductionFiberEquiv p k y).symm yFiber
  have hux :
      primePowerCoordinateLift p k x u = point.1.1.1 := by
    calc
      primePowerCoordinateLift p k x u =
          (primePowerCoordinateReductionFiberEquiv p k x u).1 :=
        (primePowerCoordinateReductionFiberEquiv_apply_val p k x u).symm
      _ = xFiber.1 :=
        congrArg Subtype.val
          ((primePowerCoordinateReductionFiberEquiv p k x).apply_symm_apply
            xFiber)
      _ = point.1.1.1 := rfl
  have hvy :
      primePowerCoordinateLift p k y v = point.1.1.2 := by
    calc
      primePowerCoordinateLift p k y v =
          (primePowerCoordinateReductionFiberEquiv p k y v).1 :=
        (primePowerCoordinateReductionFiberEquiv_apply_val p k y v).symm
      _ = yFiber.1 :=
        congrArg Subtype.val
          ((primePowerCoordinateReductionFiberEquiv p k y).apply_symm_apply
            yFiber)
      _ = point.1.1.2 := rfl
  have hcurve :
      shortWeierstrassResidual a b
        (primePowerCoordinateLift p k x u,
          primePowerCoordinateLift p k y v) = 0 := by
    rw [hux, hvy]
    exact point.1.2
  have hz :
      (shortWeierstrassResidualInt a b
          (x + (p : ℤ) ^ k * (ZMod.cast u : ℤ))
          (y + (p : ℤ) ^ k * (ZMod.cast v : ℤ)) :
        ZMod (p ^ (k + 1))) = 0 := by
    change
      shortWeierstrassResidual a b
        (((x + (p : ℤ) ^ k * (ZMod.cast u : ℤ) : ℤ) :
            ZMod (p ^ (k + 1))),
          ((y + (p : ℤ) ^ k * (ZMod.cast v : ℤ) : ℤ) :
            ZMod (p ^ (k + 1)))) = 0 at hcurve
    rw [shortWeierstrassResidual_intCast] at hcurve
    exact hcurve
  have hdiv :
      (((p ^ (k + 1) : ℕ) : ℤ) ∣
        shortWeierstrassResidualInt a b
          (x + (p : ℤ) ^ k * (ZMod.cast u : ℤ))
          (y + (p : ℤ) ^ k * (ZMod.cast v : ℤ))) :=
    (CharP.intCast_eq_zero_iff
      (ZMod (p ^ (k + 1))) (p ^ (k + 1)) _).1 hz
  have hraw :
      (p : ℤ) ^ (k + 1) ∣
        shortWeierstrassResidualInt a b
          (x + (p : ℤ) ^ k * (ZMod.cast u : ℤ))
          (y + (p : ℤ) ^ k * (ZMod.cast v : ℤ)) := by
    simpa only [Nat.cast_pow] using hdiv
  let uv : RawWeierstrassLiftFiber p k a b x y :=
    ⟨(u, v), hraw⟩
  refine ⟨uv, ?_⟩
  apply Subtype.ext
  apply Subtype.ext
  apply Prod.ext
  · simpa [uv] using hux
  · simpa [uv] using hvy

/--
The raw Taylor increment fiber is canonically equivalent to the intrinsic
`MapFiber` of affine reduction.
-/
def rawWeierstrassLiftFiberEquivPrimePowerReduction
    (p k : ℕ) [Fact (Nat.Prime p)]
    (a b x y : ℤ)
    (target : AffineCongruenceState (p ^ k) a b)
    (hx : (x : ZMod (p ^ k)) = target.1.1)
    (hy : (y : ZMod (p ^ k)) = target.1.2) :
    RawWeierstrassLiftFiber p k a b x y ≃
      MapFiber
        (affineCongruenceStateReduction
          (primePowerStepDvd p k) a b)
        target :=
  Equiv.ofBijective
    (rawWeierstrassLiftFiberMap p k a b x y target hx hy)
    ⟨rawWeierstrassLiftFiberMap_injective p k a b x y target hx hy,
      rawWeierstrassLiftFiberMap_surjective p k a b x y target hx hy⟩

/--
Two integral representatives of the same target state yield equivalent raw
increment fibers.  Both are identified with the same intrinsic reduction
fiber, so representative independence is not an extra counting assumption.
-/
def rawWeierstrassLiftFiberRepresentativeEquiv
    (p k : ℕ) [Fact (Nat.Prime p)]
    (a b x y x' y' : ℤ)
    (target : AffineCongruenceState (p ^ k) a b)
    (hx : (x : ZMod (p ^ k)) = target.1.1)
    (hy : (y : ZMod (p ^ k)) = target.1.2)
    (hx' : (x' : ZMod (p ^ k)) = target.1.1)
    (hy' : (y' : ZMod (p ^ k)) = target.1.2) :
    RawWeierstrassLiftFiber p k a b x y ≃
      RawWeierstrassLiftFiber p k a b x' y' :=
  (rawWeierstrassLiftFiberEquivPrimePowerReduction
      p k a b x y target hx hy).trans
    (rawWeierstrassLiftFiberEquivPrimePowerReduction
      p k a b x' y' target hx' hy').symm

end

end CPFormal.Elliptic
