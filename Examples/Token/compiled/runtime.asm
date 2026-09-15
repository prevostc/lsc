// Labelled pre-assembly (powdr YulEvmCompiler.Asm, before lowerProg).
// Each `Ln:` is a JUMPDEST. JUMP/JUMPI take labels, not byte offsets.
// selector → function  (hex and decimal; `switch` cases print decimal)
//   0xa9059cbb  (2835717307)  transfer(address,uint256)
//   0x23b872dd  (599290589)  transferFrom(address,address,uint256)
//   0x095ea7b3  (157198259)  approve(address,uint256)
//   0x18160ddd  (404098525)  totalSupply()
//   0x70a08231  (1889567281)  balanceOf(address)
//   0xdd62ed3e  (3714247998)  allowance(address,address)
//   0x40c10f19  (1086394137)  mint(address,uint256)
//   0x42966c68  (1117154408)  burn(uint256)

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
    PUSH 0xa9059cbb    // selector: transfer(address,uint256)
    EQ
    JUMPI L4
    DUP1
    PUSH 0x23b872dd    // selector: transferFrom(address,address,uint256)
    EQ
    JUMPI L10
    DUP1
    PUSH 0x095ea7b3    // selector: approve(address,uint256)
    EQ
    JUMPI L18
    DUP1
    PUSH 0x18160ddd    // selector: totalSupply()
    EQ
    JUMPI L21
    DUP1
    PUSH 0x70a08231    // selector: balanceOf(address)
    EQ
    JUMPI L24
    DUP1
    PUSH 0xdd62ed3e    // selector: allowance(address,address)
    EQ
    JUMPI L27
    DUP1
    PUSH 0x40c10f19    // selector: mint(address,uint256)
    EQ
    JUMPI L30
    DUP1
    PUSH 0x42966c68    // selector: burn(uint256)
    EQ
    JUMPI L36
    POP
    PUSH 0x00
    PUSH 0x00
    REVERT
    JUMP L3
L4:    // JUMPDEST
    POP
    PUSH 0x44
    CALLDATASIZE
    LT
    ISZERO
    JUMPI L5
    PUSH 0x00
    PUSH 0x00
    REVERT
L5:    // JUMPDEST
    CALLVALUE
    ISZERO
    JUMPI L6
    PUSH 0x00
    PUSH 0x00
    REVERT
L6:    // JUMPDEST
    PUSH 0x04
    CALLDATALOAD
    PUSH 0x24
    CALLDATALOAD
    CALLER
    DUP1
    PUSH 0x00
    MSTORE
    PUSH 0x02
    PUSH 0x20
    MSTORE
    PUSH 0x40
    PUSH 0x00
    KECCAK256
    SLOAD
    DUP3
    DUP2
    LT
    ISZERO
    JUMPI L7
    PUSH 0xf4d678b8    // selector: InsufficientBalance()
    PUSH 0xe0
    SHL
    PUSH 0x80
    MSTORE
    PUSH 0x04
    PUSH 0x80
    REVERT
L7:    // JUMPDEST
    DUP3
    DUP2
    LT
    ISZERO
    JUMPI L8
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
L8:    // JUMPDEST
    DUP3
    DUP2
    SUB
    DUP3
    PUSH 0x00
    MSTORE
    PUSH 0x02
    PUSH 0x20
    MSTORE
    DUP1
    PUSH 0x40
    PUSH 0x00
    KECCAK256
    SSTORE
    DUP5
    PUSH 0x00
    MSTORE
    PUSH 0x02
    PUSH 0x20
    MSTORE
    PUSH 0x40
    PUSH 0x00
    KECCAK256
    SLOAD
    DUP5
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
    DUP7
    PUSH 0x00
    MSTORE
    PUSH 0x02
    PUSH 0x20
    MSTORE
    DUP1
    PUSH 0x40
    PUSH 0x00
    KECCAK256
    SSTORE
    DUP5
    PUSH 0x80
    MSTORE
    DUP7
    PUSH 0xa0
    MSTORE
    DUP6
    PUSH 0xc0
    MSTORE
    PUSH 0xddf252ad1be2c89b69c2b068fc378daa952ba7f163c4a11628f55a4df523b3ef    // topic: Transfer(address,address,uint256)
    PUSH 0x60
    PUSH 0x80
    LOG1
    PUSH 0x01
    PUSH 0x80
    MSTORE
    PUSH 0x20
    PUSH 0x80
    RETURN
    POP
    POP
    POP
    POP
    POP
    POP
    POP
    JUMP L3
L10:    // JUMPDEST
    POP
    PUSH 0x64
    CALLDATASIZE
    LT
    ISZERO
    JUMPI L11
    PUSH 0x00
    PUSH 0x00
    REVERT
L11:    // JUMPDEST
    CALLVALUE
    ISZERO
    JUMPI L12
    PUSH 0x00
    PUSH 0x00
    REVERT
L12:    // JUMPDEST
    PUSH 0x04
    CALLDATALOAD
    PUSH 0x24
    CALLDATALOAD
    PUSH 0x44
    CALLDATALOAD
    CALLER
    DUP4
    PUSH 0x00
    MSTORE
    PUSH 0x03
    PUSH 0x20
    MSTORE
    PUSH 0x40
    PUSH 0x00
    KECCAK256
    PUSH 0x20
    MSTORE
    DUP1
    PUSH 0x00
    MSTORE
    PUSH 0x40
    PUSH 0x00
    KECCAK256
    SLOAD
    DUP3
    DUP2
    LT
    ISZERO
    JUMPI L13
    PUSH 0x13be252b    // selector: InsufficientAllowance()
    PUSH 0xe0
    SHL
    PUSH 0x80
    MSTORE
    PUSH 0x04
    PUSH 0x80
    REVERT
L13:    // JUMPDEST
    DUP5
    PUSH 0x00
    MSTORE
    PUSH 0x02
    PUSH 0x20
    MSTORE
    PUSH 0x40
    PUSH 0x00
    KECCAK256
    SLOAD
    DUP4
    DUP2
    LT
    ISZERO
    JUMPI L14
    PUSH 0xf4d678b8    // selector: InsufficientBalance()
    PUSH 0xe0
    SHL
    PUSH 0x80
    MSTORE
    PUSH 0x04
    PUSH 0x80
    REVERT
L14:    // JUMPDEST
    DUP4
    DUP3
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
    DUP4
    DUP3
    SUB
    DUP7
    PUSH 0x00
    MSTORE
    PUSH 0x03
    PUSH 0x20
    MSTORE
    PUSH 0x40
    PUSH 0x00
    KECCAK256
    PUSH 0x20
    MSTORE
    DUP4
    PUSH 0x00
    MSTORE
    DUP1
    PUSH 0x40
    PUSH 0x00
    KECCAK256
    SSTORE
    DUP5
    DUP3
    LT
    ISZERO
    JUMPI L16
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
L16:    // JUMPDEST
    DUP5
    DUP3
    SUB
    DUP8
    PUSH 0x00
    MSTORE
    PUSH 0x02
    PUSH 0x20
    MSTORE
    DUP1
    PUSH 0x40
    PUSH 0x00
    KECCAK256
    SSTORE
    DUP7
    PUSH 0x00
    MSTORE
    PUSH 0x02
    PUSH 0x20
    MSTORE
    PUSH 0x40
    PUSH 0x00
    KECCAK256
    SLOAD
    DUP7
    DUP2
    ADD
    DUP2
    DUP2
    LT
    ISZERO
    JUMPI L17
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
L17:    // JUMPDEST
    DUP9
    PUSH 0x00
    MSTORE
    PUSH 0x02
    PUSH 0x20
    MSTORE
    DUP1
    PUSH 0x40
    PUSH 0x00
    KECCAK256
    SSTORE
    DUP10
    PUSH 0x80
    MSTORE
    DUP9
    PUSH 0xa0
    MSTORE
    DUP8
    PUSH 0xc0
    MSTORE
    PUSH 0xddf252ad1be2c89b69c2b068fc378daa952ba7f163c4a11628f55a4df523b3ef    // topic: Transfer(address,address,uint256)
    PUSH 0x60
    PUSH 0x80
    LOG1
    PUSH 0x01
    PUSH 0x80
    MSTORE
    PUSH 0x20
    PUSH 0x80
    RETURN
    POP
    POP
    POP
    POP
    POP
    POP
    POP
    POP
    POP
    POP
    JUMP L3
L18:    // JUMPDEST
    POP
    PUSH 0x44
    CALLDATASIZE
    LT
    ISZERO
    JUMPI L19
    PUSH 0x00
    PUSH 0x00
    REVERT
L19:    // JUMPDEST
    CALLVALUE
    ISZERO
    JUMPI L20
    PUSH 0x00
    PUSH 0x00
    REVERT
L20:    // JUMPDEST
    PUSH 0x04
    CALLDATALOAD
    PUSH 0x24
    CALLDATALOAD
    CALLER
    DUP1
    PUSH 0x00
    MSTORE
    PUSH 0x03
    PUSH 0x20
    MSTORE
    PUSH 0x40
    PUSH 0x00
    KECCAK256
    PUSH 0x20
    MSTORE
    DUP3
    PUSH 0x00
    MSTORE
    DUP2
    PUSH 0x40
    PUSH 0x00
    KECCAK256
    SSTORE
    DUP1
    PUSH 0x80
    MSTORE
    DUP3
    PUSH 0xa0
    MSTORE
    DUP2
    PUSH 0xc0
    MSTORE
    PUSH 0x8c5be1e5ebec7d5bd14f71427d1e84f3dd0314c0f7b2291e5b200ac8c7c3b925    // topic: Approval(address,address,uint256)
    PUSH 0x60
    PUSH 0x80
    LOG1
    PUSH 0x01
    PUSH 0x80
    MSTORE
    PUSH 0x20
    PUSH 0x80
    RETURN
    POP
    POP
    POP
    JUMP L3
L21:    // JUMPDEST
    POP
    PUSH 0x04
    CALLDATASIZE
    LT
    ISZERO
    JUMPI L22
    PUSH 0x00
    PUSH 0x00
    REVERT
L22:    // JUMPDEST
    CALLVALUE
    ISZERO
    JUMPI L23
    PUSH 0x00
    PUSH 0x00
    REVERT
L23:    // JUMPDEST
    PUSH 0x01
    SLOAD
    DUP1
    PUSH 0x80
    MSTORE
    PUSH 0x20
    PUSH 0x80
    RETURN
    POP
    JUMP L3
L24:    // JUMPDEST
    POP
    PUSH 0x24
    CALLDATASIZE
    LT
    ISZERO
    JUMPI L25
    PUSH 0x00
    PUSH 0x00
    REVERT
L25:    // JUMPDEST
    CALLVALUE
    ISZERO
    JUMPI L26
    PUSH 0x00
    PUSH 0x00
    REVERT
L26:    // JUMPDEST
    PUSH 0x04
    CALLDATALOAD
    DUP1
    PUSH 0x00
    MSTORE
    PUSH 0x02
    PUSH 0x20
    MSTORE
    PUSH 0x40
    PUSH 0x00
    KECCAK256
    SLOAD
    DUP1
    PUSH 0x80
    MSTORE
    PUSH 0x20
    PUSH 0x80
    RETURN
    POP
    POP
    JUMP L3
L27:    // JUMPDEST
    POP
    PUSH 0x44
    CALLDATASIZE
    LT
    ISZERO
    JUMPI L28
    PUSH 0x00
    PUSH 0x00
    REVERT
L28:    // JUMPDEST
    CALLVALUE
    ISZERO
    JUMPI L29
    PUSH 0x00
    PUSH 0x00
    REVERT
L29:    // JUMPDEST
    PUSH 0x04
    CALLDATALOAD
    PUSH 0x24
    CALLDATALOAD
    DUP2
    PUSH 0x00
    MSTORE
    PUSH 0x03
    PUSH 0x20
    MSTORE
    PUSH 0x40
    PUSH 0x00
    KECCAK256
    PUSH 0x20
    MSTORE
    DUP1
    PUSH 0x00
    MSTORE
    PUSH 0x40
    PUSH 0x00
    KECCAK256
    SLOAD
    DUP1
    PUSH 0x80
    MSTORE
    PUSH 0x20
    PUSH 0x80
    RETURN
    POP
    POP
    POP
    JUMP L3
L30:    // JUMPDEST
    POP
    PUSH 0x44
    CALLDATASIZE
    LT
    ISZERO
    JUMPI L31
    PUSH 0x00
    PUSH 0x00
    REVERT
L31:    // JUMPDEST
    CALLVALUE
    ISZERO
    JUMPI L32
    PUSH 0x00
    PUSH 0x00
    REVERT
L32:    // JUMPDEST
    PUSH 0x04
    CALLDATALOAD
    PUSH 0x24
    CALLDATALOAD
    CALLER
    PUSH 0x00
    SLOAD
    DUP1
    DUP3
    EQ
    JUMPI L33
    PUSH 0x30cd7471    // selector: NotOwner()
    PUSH 0xe0
    SHL
    PUSH 0x80
    MSTORE
    PUSH 0x04
    PUSH 0x80
    REVERT
L33:    // JUMPDEST
    PUSH 0x01
    SLOAD
    DUP4
    DUP2
    ADD
    DUP2
    DUP2
    LT
    ISZERO
    JUMPI L34
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
L34:    // JUMPDEST
    DUP1
    PUSH 0x01
    SSTORE
    DUP6
    PUSH 0x00
    MSTORE
    PUSH 0x02
    PUSH 0x20
    MSTORE
    PUSH 0x40
    PUSH 0x00
    KECCAK256
    SLOAD
    DUP6
    DUP2
    ADD
    DUP2
    DUP2
    LT
    ISZERO
    JUMPI L35
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
L35:    // JUMPDEST
    DUP8
    PUSH 0x00
    MSTORE
    PUSH 0x02
    PUSH 0x20
    MSTORE
    DUP1
    PUSH 0x40
    PUSH 0x00
    KECCAK256
    SSTORE
    PUSH 0x00
    PUSH 0x80
    MSTORE
    DUP8
    PUSH 0xa0
    MSTORE
    DUP7
    PUSH 0xc0
    MSTORE
    PUSH 0xddf252ad1be2c89b69c2b068fc378daa952ba7f163c4a11628f55a4df523b3ef    // topic: Transfer(address,address,uint256)
    PUSH 0x60
    PUSH 0x80
    LOG1
    STOP
    POP
    POP
    POP
    POP
    POP
    POP
    POP
    POP
    JUMP L3
L36:    // JUMPDEST
    POP
    PUSH 0x24
    CALLDATASIZE
    LT
    ISZERO
    JUMPI L37
    PUSH 0x00
    PUSH 0x00
    REVERT
L37:    // JUMPDEST
    CALLVALUE
    ISZERO
    JUMPI L38
    PUSH 0x00
    PUSH 0x00
    REVERT
L38:    // JUMPDEST
    PUSH 0x04
    CALLDATALOAD
    CALLER
    DUP1
    PUSH 0x00
    MSTORE
    PUSH 0x02
    PUSH 0x20
    MSTORE
    PUSH 0x40
    PUSH 0x00
    KECCAK256
    SLOAD
    DUP3
    DUP2
    LT
    ISZERO
    DUP1
    PUSH 0x00
    EQ
    JUMPI L40
    POP
    DUP3
    DUP2
    LT
    ISZERO
    JUMPI L41
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
L41:    // JUMPDEST
    DUP3
    DUP2
    SUB
    DUP3
    PUSH 0x00
    MSTORE
    PUSH 0x02
    PUSH 0x20
    MSTORE
    DUP1
    PUSH 0x40
    PUSH 0x00
    KECCAK256
    SSTORE
    PUSH 0x01
    SLOAD
    DUP5
    DUP2
    LT
    ISZERO
    JUMPI L42
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
L42:    // JUMPDEST
    DUP5
    DUP2
    SUB
    DUP1
    PUSH 0x01
    SSTORE
    POP
    POP
    POP
    JUMP L39
L40:    // JUMPDEST
    POP
    PUSH 0xf4d678b8    // selector: InsufficientBalance()
    PUSH 0xe0
    SHL
    PUSH 0x80
    MSTORE
    PUSH 0x04
    PUSH 0x80
    REVERT
L39:    // JUMPDEST
    DUP2
    PUSH 0x80
    MSTORE
    PUSH 0x00
    PUSH 0xa0
    MSTORE
    DUP3
    PUSH 0xc0
    MSTORE
    PUSH 0xddf252ad1be2c89b69c2b068fc378daa952ba7f163c4a11628f55a4df523b3ef    // topic: Transfer(address,address,uint256)
    PUSH 0x60
    PUSH 0x80
    LOG1
    STOP
    POP
    POP
    POP
L3:    // JUMPDEST
