import Mathlib.Data.Nat.GCD.Basic

/- Finite periodic case certificate for the reduced Type I middle case.
   This file does NOT formalize the reduction from prime sources, the period
   lifting argument, the j=0/j=2 paper proofs, or Erdos-Straus. -/
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace LargePrimeSource20261116

def hardResidues : List Nat := [1, 121, 169, 289, 361, 529]

def localPass (s sigma alpha beta h p : Nat) : Bool :=
  let qNum := alpha * p + beta
  let qDen := h * sigma
  let q := qNum / qDen
  let rNum := (h + alpha) * p + beta
  let rDen := 4 * h * s
  let r := rNum / rDen
  qNum % qDen == 0 &&
  q % 4 == (if sigma == 1 then 3 else 1) &&
  Nat.gcd q 210 == 1 &&
  rNum % rDen == 0 &&
  Nat.gcd r 210 == 1

def casePass (s sigma alpha beta h : Nat) : Bool :=
  if alpha >= sigma * h || 4 * h * s > 9 * (h + alpha) then true
  else (List.range (h * s * sigma)).all fun t =>
    hardResidues.all fun a => !(localPass s sigma alpha beta h (840*t+a))

def periodicCover : Bool :=
  (List.range 8).all fun s0 =>
    let s := s0 + 1
    [1, 3].all fun sigma =>
      (List.range 8).all fun alpha0 =>
        let alpha := alpha0 + 1
        (List.range 8).all fun beta0 =>
          let beta := beta0 + 1
          if s % (alpha * beta) == 0 && Nat.gcd alpha beta == 1 then
            (List.range (3*alpha)).all fun h0 =>
              casePass s sigma alpha beta (h0+1)
          else true

theorem periodic_cover_valid : periodicCover = true := by decide

#print axioms periodic_cover_valid

end LargePrimeSource20261116
