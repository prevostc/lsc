// Labelled pre-assembly (powdr YulEvmCompiler.Asm, before lowerProg).
// Each `Ln:` is a JUMPDEST. JUMP/JUMPI take labels, not byte offsets.
// selector → function  (hex and decimal; `switch` cases print decimal)
//   0xd09de08a  (3500007562)  increment()
//   0x03df179c  (64952220)  incrementBy(uint256)
//   0x2baeceb7  (732876471)  decrement()
//   0x6d4ce63c  (1833756220)  get()

    PUSH 0x0100
    ISZERO
    POP
    PUSH 0x04
    CALLDATASIZE
    LT
    ISZERO
    JUMPI L1
    PUSH 0x00
    PUSH 0x00
    REVERT
L1:    // JUMPDEST
    PUSH 0x00
    CALLDATALOAD
    PUSH 0xe0
    SHR
    DUP1
    PUSH 0xd09de08a    // selector: increment()
    EQ
    JUMPI L3
    DUP1
    PUSH 0x03df179c    // selector: incrementBy(uint256)
    EQ
    JUMPI L6
    DUP1
    PUSH 0x2baeceb7    // selector: decrement()
    EQ
    JUMPI L10
    DUP1
    PUSH 0x6d4ce63c    // selector: get()
    EQ
    JUMPI L15
    POP
    PUSH 0x00
    PUSH 0x00
    REVERT
    JUMP L2
L3:    // JUMPDEST
    POP
    PUSH 0x04
    CALLDATASIZE
    LT
    ISZERO
    JUMPI L4
    PUSH 0x00
    PUSH 0x00
    REVERT
L4:    // JUMPDEST
    PUSH 0x00
    SLOAD
    PUSH 0x01
    DUP2
    ADD
    DUP2
    DUP2
    LT
    ISZERO
    JUMPI L5
    PUSH 0x4e487b71
    PUSH 0xe0
    SHL
    PUSH 0x80
    MSTORE
    PUSH 0x11
    PUSH 0x84
    MSTORE
    PUSH 0x24
    PUSH 0x80
    REVERT
L5:    // JUMPDEST
    DUP1
    PUSH 0x00
    SSTORE
    PUSH 0x01
    PUSH 0x80
    MSTORE
    PUSH 0x20d8a6f5a693f9d1d627a598e8820f7a55ee74c183aa8f1a30e8d4e8dd9a8d84    // topic: Incremented(uint256)
    PUSH 0x20
    PUSH 0x80
    LOG1
    STOP
    POP
    POP
    JUMP L2
L6:    // JUMPDEST
    POP
    PUSH 0x24
    CALLDATASIZE
    LT
    ISZERO
    JUMPI L7
    PUSH 0x00
    PUSH 0x00
    REVERT
L7:    // JUMPDEST
    PUSH 0x04
    CALLDATALOAD
    PUSH 0x00
    DUP2
    EQ
    ISZERO
    JUMPI L8
    PUSH 0xf4560403    // selector: Zero()
    PUSH 0xe0
    SHL
    PUSH 0x80
    MSTORE
    PUSH 0x04
    PUSH 0x80
    REVERT
L8:    // JUMPDEST
    PUSH 0x00
    SLOAD
    DUP2
    DUP2
    ADD
    DUP2
    DUP2
    LT
    ISZERO
    JUMPI L9
    PUSH 0x4e487b71
    PUSH 0xe0
    SHL
    PUSH 0x80
    MSTORE
    PUSH 0x11
    PUSH 0x84
    MSTORE
    PUSH 0x24
    PUSH 0x80
    REVERT
L9:    // JUMPDEST
    DUP1
    PUSH 0x00
    SSTORE
    DUP3
    PUSH 0x80
    MSTORE
    PUSH 0x20d8a6f5a693f9d1d627a598e8820f7a55ee74c183aa8f1a30e8d4e8dd9a8d84    // topic: Incremented(uint256)
    PUSH 0x20
    PUSH 0x80
    LOG1
    STOP
    POP
    POP
    POP
    JUMP L2
L10:    // JUMPDEST
    POP
    PUSH 0x04
    CALLDATASIZE
    LT
    ISZERO
    JUMPI L11
    PUSH 0x00
    PUSH 0x00
    REVERT
L11:    // JUMPDEST
    PUSH 0x00
    SLOAD
    PUSH 0x00
    DUP2
    EQ
    DUP1
    PUSH 0x00
    EQ
    JUMPI L13
    POP
    PUSH 0x00
    DUP1
    PUSH 0x00
    SSTORE
    STOP
    POP
    JUMP L12
L13:    // JUMPDEST
    POP
    PUSH 0x01
    DUP2
    LT
    ISZERO
    JUMPI L14
    PUSH 0x4e487b71
    PUSH 0xe0
    SHL
    PUSH 0x80
    MSTORE
    PUSH 0x11
    PUSH 0x84
    MSTORE
    PUSH 0x24
    PUSH 0x80
    REVERT
L14:    // JUMPDEST
    PUSH 0x01
    DUP2
    SUB
    DUP1
    PUSH 0x00
    SSTORE
    STOP
    POP
L12:    // JUMPDEST
    POP
    JUMP L2
L15:    // JUMPDEST
    POP
    PUSH 0x04
    CALLDATASIZE
    LT
    ISZERO
    JUMPI L16
    PUSH 0x00
    PUSH 0x00
    REVERT
L16:    // JUMPDEST
    PUSH 0x00
    SLOAD
    DUP1
    PUSH 0x80
    MSTORE
    PUSH 0x20
    PUSH 0x80
    RETURN
    POP
L2:    // JUMPDEST
