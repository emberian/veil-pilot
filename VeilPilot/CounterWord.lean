module
public import Veil

/-! # The counter word: why Ariadne flips one bit per increment

Ariadne (§4.2) stores its monotonic counter as a Gray code so that every increment is a single bit
flip, which non-volatile memory performs atomically; a power loss leaves either the old or the new
value. A plain binary word changes several bits per increment (011 → 100), the cells are written one
at a time, and a crash in between leaves a word that decodes to neither: below the old value, or
above the new one.

`flip` changes one differing bit at a time, in any order the hardware likes; `crash` may come between
any two flips. The property: a reader after any crash sees the last completed value or the next one,
never anything else. (Reflected Gray code here; Ariadne's balanced Gray code spreads the wear, which
does not change the one-flip property.)
-/

public section

def grayEnc (v : Nat) : Nat := v ^^^ (v >>> 1)

def grayDecGo (acc s : Nat) : Nat :=
  if _h : s = 0 then acc else grayDecGo (acc ^^^ s) (s >>> 1)
termination_by s
decreasing_by simp only [Nat.shiftRight_eq_div_pow, Nat.pow_one]; omega

def grayDec (w : Nat) : Nat := grayDecGo w (w >>> 1)

end

veil module CounterWord

public instance (n : Nat) (p : Nat → Prop) [DecidablePred p] :
    Veil.Enumeration {a : Nat // a < n ∧ p a} where
  allValues := ((List.range n).filter p).attachWith _ (by simp)
  complete := by simp

param gray : Bool
param width : Nat

individual word : Nat
individual done : Nat
individual target : Nat
individual busy : Bool

#gen_state

after_init {
  word := 0
  done := 0
  target := 0
  busy := false
}

action startInc {
  require ¬ busy ∧ done + 2 < 2 ^ width
  target := done + 1
  busy := true
}

action flip {
  require busy
  let enc := if gray then grayEnc target else target
  let i :| i < width ∧ ((word ^^^ enc) >>> i) % 2 = 1
  word := word ^^^ (1 <<< i)
  if word = enc then
    done := target
    busy := false
}

action crash {
  require busy
  busy := false
}

-- what a reader decodes after a crash: the completed value or the one being written
safety [read_is_old_or_new]
  ¬ busy → ((if gray then grayDec word else word) = done)

#gen_spec

set_option veil.violationIsError false in
#model_check { gray := false, width := 3 } {}
set_option veil.violationIsError false in
#model_check { gray := true, width := 3 } {}

end CounterWord
