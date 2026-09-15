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
    PUSH 0x00
    TLOAD
    ISZERO
    JUMPI L1
    PUSH 0x00
    PUSH 0x00
    REVERT
L1:    // JUMPDEST
    PUSH 0x04
    CALLDATASIZE
    LT
    ISZERO
    JUMPI L2
    PUSH 0x00
    PUSH 0x00
    REVERT
L2:    // JUMPDEST
    PUSH 0x00
    CALLDATALOAD
    PUSH 0xe0
    SHR
    DUP1
    PUSH 0xd09de08a    // selector: increment()
    EQ
    JUMPI L4
    DUP1
    PUSH 0x03df179c    // selector: incrementBy(uint256)
    EQ
    JUMPI L7
    DUP1
    PUSH 0x2baeceb7    // selector: decrement()
    EQ
    JUMPI L11
    DUP1
    PUSH 0x6d4ce63c    // selector: get()
    EQ
    JUMPI L16
    POP
    PUSH 0x00
    PUSH 0x00
    REVERT
    JUMP L3
L4:    // JUMPDEST
    POP
    PUSH 0x04
    CALLDATASIZE
    LT
    ISZERO
    JUMPI L5
    PUSH 0x00
    PUSH 0x00
    REVERT
L5:    // JUMPDEST
    PUSH 0x00
    SLOAD
    PUSH 0x01
    DUP2
    ADD
    DUP2
    DUP2
    LT
    ISZERO
    JUMPI L6
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
L6:    // JUMPDEST
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
    JUMP L3
L7:    // JUMPDEST
    POP
    PUSH 0x24
    CALLDATASIZE
    LT
    ISZERO
    JUMPI L8
    PUSH 0x00
    PUSH 0x00
    REVERT
L8:    // JUMPDEST
    PUSH 0x04
    CALLDATALOAD
    PUSH 0x00
    DUP2
    EQ
    ISZERO
    JUMPI L9
    PUSH 0xf4560403    // selector: Zero()
    PUSH 0xe0
    SHL
    PUSH 0x80
    MSTORE
    PUSH 0x04
    PUSH 0x80
    REVERT
L9:    // JUMPDEST
    PUSH 0x00
    SLOAD
    DUP2
    DUP2
    ADD
    DUP2
    DUP2
    LT
    ISZERO
    JUMPI L10
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
L10:    // JUMPDEST
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
    JUMP L3
L11:    // JUMPDEST
    POP
    PUSH 0x04
    CALLDATASIZE
    LT
    ISZERO
    JUMPI L12
    PUSH 0x00
    PUSH 0x00
    REVERT
L12:    // JUMPDEST
    PUSH 0x00
    SLOAD
    PUSH 0x00
    PUSH 0x00
    PUSH 0x00
    DUP4
    EQ
    DUP1
    PUSH 0x00
    EQ
    JUMPI L14
    POP
    PUSH 0x00
    DUP1
    SWAP2
    POP
    POP
    JUMP L13
L14:    // JUMPDEST
    POP
    PUSH 0x01
    DUP4
    LT
    ISZERO
    JUMPI L15
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
L15:    // JUMPDEST
    PUSH 0x01
    DUP4
    SUB
    DUP1
    SWAP2
    POP
    POP
L13:    // JUMPDEST
    DUP1
    SWAP2
    POP
    POP
    DUP1
    PUSH 0x00
    SSTORE
    STOP
    POP
    POP
    JUMP L3
L16:    // JUMPDEST
    POP
    PUSH 0x04
    CALLDATASIZE
    LT
    ISZERO
    JUMPI L17
    PUSH 0x00
    PUSH 0x00
    REVERT
L17:    // JUMPDEST
    PUSH 0x00
    SLOAD
    DUP1
    PUSH 0x80
    MSTORE
    PUSH 0x20
    PUSH 0x80
    RETURN
    POP
L3:    // JUMPDEST
