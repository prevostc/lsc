import Counter
import CounterProofs
import LscV2.Lang.Eval

open LscV2 Counter

theorem increment_increases_number_when_not_paused
    (s s' : ContractState CounterStorage) (log : List CounterEvent)
    (hpaused : ¬ s.storage.paused)
    (hno : s.storage.number.raw.toNat + 1 < 2 ^ 256)
    (h : runS increment s = .ok ((), s', log)) :
    s'.storage.number.raw.toNat = s.storage.number.raw.toNat + 1 :=
  CounterProofs.increment_increases_number_when_not_paused s s' log hpaused hno h

theorem increment_errors_when_paused
    (s : ContractState CounterStorage) (hp : s.storage.paused) :
    runS increment s = .error CounterError.Paused :=
  CounterProofs.increment_errors_when_paused s hp

theorem increment_does_not_change_paused
    (s s' : ContractState CounterStorage) (log : List CounterEvent)
    (hpaused : ¬ s.storage.paused)
    (hno : s.storage.number.raw.toNat + 1 < 2 ^ 256)
    (h : runS increment s = .ok ((), s', log)) :
    s'.storage.paused = s.storage.paused :=
  CounterProofs.increment_does_not_change_paused s s' log hpaused hno h

theorem increment_does_not_change_owner
    (s s' : ContractState CounterStorage) (log : List CounterEvent)
    (hpaused : ¬ s.storage.paused)
    (hno : s.storage.number.raw.toNat + 1 < 2 ^ 256)
    (h : runS increment s = .ok ((), s', log)) :
    s'.storage.owner = s.storage.owner :=
  CounterProofs.increment_does_not_change_owner s s' log hpaused hno h

theorem increment_emits_incremented
    (s s' : ContractState CounterStorage) (log : List CounterEvent)
    (hpaused : ¬ s.storage.paused)
    (hno : s.storage.number.raw.toNat + 1 < 2 ^ 256)
    (h : runS increment s = .ok ((), s', log)) :
    log = [CounterEvent.Incremented s'.storage.number] :=
  CounterProofs.increment_emits_incremented s s' log hpaused hno h

theorem increment_reverts_on_overflow
    (s : ContractState CounterStorage)
    (hpaused : ¬ s.storage.paused)
    (hov : ¬ s.storage.number.raw.toNat + 1 < 2 ^ 256) :
    runS increment s = .error CounterError.Overflow :=
  CounterProofs.increment_reverts_on_overflow s hpaused hov
