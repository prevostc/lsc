// Labelled pre-assembly (powdr YulEvmCompiler.Asm, before lowerProg).
// Each `Ln:` is a JUMPDEST. JUMP/JUMPI take labels, not byte offsets.
// selector → function  (hex and decimal; `switch` cases print decimal)
//   0xd0e30db0  (3504541104)  deposit()
//   0x2e1a7d4d  (773487949)  withdraw(uint256)
//   0xa9059cbb  (2835717307)  transfer(address,uint256)
//   0x23b872dd  (599290589)  transferFrom(address,address,uint256)
//   0x095ea7b3  (157198259)  approve(address,uint256)
//   0x18160ddd  (404098525)  totalSupply()
//   0x70a08231  (1889567281)  balanceOf(address)
//   0xdd62ed3e  (3714247998)  allowance(address,address)

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
    PUSH 0xd0e30db0    // selector: deposit()
    EQ
    JUMPI L4
    DUP1
    PUSH 0x2e1a7d4d    // selector: withdraw(uint256)
    EQ
    JUMPI L9
    DUP1
    PUSH 0xa9059cbb    // selector: transfer(address,uint256)
    EQ
    JUMPI L15
    DUP1
    PUSH 0x23b872dd    // selector: transferFrom(address,address,uint256)
    EQ
    JUMPI L21
    DUP1
    PUSH 0x095ea7b3    // selector: approve(address,uint256)
    EQ
    JUMPI L29
    DUP1
    PUSH 0x18160ddd    // selector: totalSupply()
    EQ
    JUMPI L32
    DUP1
    PUSH 0x70a08231    // selector: balanceOf(address)
    EQ
    JUMPI L35
    DUP1
    PUSH 0xdd62ed3e    // selector: allowance(address,address)
    EQ
    JUMPI L38
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
    CALLVALUE
    SELFBALANCE
    LT
    ISZERO
    JUMPI L6
    PUSH 0x00
    PUSH 0x00
    REVERT
L6:    // JUMPDEST
    CALLER
    CALLVALUE
    DUP2
    PUSH 0x00
    MSTORE
    PUSH 0x00
    PUSH 0x20
    MSTORE
    PUSH 0x40
    PUSH 0x00
    KECCAK256
    SLOAD
    DUP2
    DUP2
    ADD
    DUP2
    DUP2
    LT
    ISZERO
    JUMPI L7
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
L7:    // JUMPDEST
    DUP4
    PUSH 0x00
    MSTORE
    PUSH 0x00
    PUSH 0x20
    MSTORE
    DUP1
    PUSH 0x40
    PUSH 0x00
    KECCAK256
    SSTORE
    PUSH 0x02
    SLOAD
    DUP4
    DUP2
    ADD
    DUP2
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
    DUP1
    PUSH 0x02
    SSTORE
    DUP6
    PUSH 0x80
    MSTORE
    DUP5
    PUSH 0xa0
    MSTORE
    PUSH 0xe1fffcc4923d04b559f4d29a8bfc6cda04eb5b0d3c460751c2402c5c5cc9109c    // topic: Deposit(address,uint256)
    PUSH 0x40
    PUSH 0x80
    LOG1
    STOP
    POP
    POP
    POP
    POP
    POP
    POP
    JUMP L3
L9:    // JUMPDEST
    POP
    PUSH 0x24
    CALLDATASIZE
    LT
    ISZERO
    JUMPI L10
    PUSH 0x00
    PUSH 0x00
    REVERT
L10:    // JUMPDEST
    CALLVALUE
    ISZERO
    JUMPI L11
    PUSH 0x00
    PUSH 0x00
    REVERT
L11:    // JUMPDEST
    PUSH 0x01
    PUSH 0x00
    TSTORE
    PUSH 0x04
    CALLDATALOAD
    CALLER
    DUP1
    PUSH 0x00
    MSTORE
    PUSH 0x00
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
    JUMPI L12
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
L12:    // JUMPDEST
    DUP3
    DUP2
    SUB
    DUP3
    PUSH 0x00
    MSTORE
    PUSH 0x00
    PUSH 0x20
    MSTORE
    DUP1
    PUSH 0x40
    PUSH 0x00
    KECCAK256
    SSTORE
    PUSH 0x02
    SLOAD
    DUP5
    DUP2
    LT
    ISZERO
    JUMPI L13
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
L13:    // JUMPDEST
    DUP5
    DUP2
    SUB
    DUP1
    PUSH 0x02
    SSTORE
    PUSH 0x00
    PUSH 0x00
    PUSH 0x00
    PUSH 0x00
    PUSH 0x00
    DUP11
    DUP11
    PUSH 0x0f4240
    CALL
    DUP1
    SWAP2
    POP
    POP
    PUSH 0x01
    DUP2
    EQ
    JUMPI L14
    PUSH 0x90b8ec18    // selector: TransferFailed()
    PUSH 0xe0
    SHL
    PUSH 0x80
    MSTORE
    PUSH 0x04
    PUSH 0x80
    REVERT
L14:    // JUMPDEST
    DUP6
    PUSH 0x80
    MSTORE
    DUP7
    PUSH 0xa0
    MSTORE
    PUSH 0x7fcf532c15f0a6db0bd6d0e038bea71d30d808c7d98cb3bf7268a95bf5081b65    // topic: Withdrawal(address,uint256)
    PUSH 0x40
    PUSH 0x80
    LOG1
    PUSH 0x00
    PUSH 0x00
    TSTORE
    STOP
    POP
    POP
    POP
    POP
    POP
    POP
    POP
    JUMP L3
L15:    // JUMPDEST
    POP
    PUSH 0x44
    CALLDATASIZE
    LT
    ISZERO
    JUMPI L16
    PUSH 0x00
    PUSH 0x00
    REVERT
L16:    // JUMPDEST
    CALLVALUE
    ISZERO
    JUMPI L17
    PUSH 0x00
    PUSH 0x00
    REVERT
L17:    // JUMPDEST
    PUSH 0x04
    CALLDATALOAD
    PUSH 0x24
    CALLDATALOAD
    CALLER
    DUP1
    PUSH 0x00
    MSTORE
    PUSH 0x00
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
    JUMPI L18
    PUSH 0xf4d678b8    // selector: InsufficientBalance()
    PUSH 0xe0
    SHL
    PUSH 0x80
    MSTORE
    PUSH 0x04
    PUSH 0x80
    REVERT
L18:    // JUMPDEST
    DUP3
    DUP2
    LT
    ISZERO
    JUMPI L19
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
L19:    // JUMPDEST
    DUP3
    DUP2
    SUB
    DUP3
    PUSH 0x00
    MSTORE
    PUSH 0x00
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
    PUSH 0x00
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
    JUMPI L20
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
L20:    // JUMPDEST
    DUP7
    PUSH 0x00
    MSTORE
    PUSH 0x00
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
L21:    // JUMPDEST
    POP
    PUSH 0x64
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
    PUSH 0x01
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
    JUMPI L24
    PUSH 0x13be252b    // selector: InsufficientAllowance()
    PUSH 0xe0
    SHL
    PUSH 0x80
    MSTORE
    PUSH 0x04
    PUSH 0x80
    REVERT
L24:    // JUMPDEST
    DUP5
    PUSH 0x00
    MSTORE
    PUSH 0x00
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
    JUMPI L25
    PUSH 0xf4d678b8    // selector: InsufficientBalance()
    PUSH 0xe0
    SHL
    PUSH 0x80
    MSTORE
    PUSH 0x04
    PUSH 0x80
    REVERT
L25:    // JUMPDEST
    DUP4
    DUP3
    LT
    ISZERO
    JUMPI L26
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
L26:    // JUMPDEST
    DUP4
    DUP3
    SUB
    DUP7
    PUSH 0x00
    MSTORE
    PUSH 0x01
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
    JUMPI L27
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
L27:    // JUMPDEST
    DUP5
    DUP3
    SUB
    DUP8
    PUSH 0x00
    MSTORE
    PUSH 0x00
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
    PUSH 0x00
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
    JUMPI L28
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
L28:    // JUMPDEST
    DUP9
    PUSH 0x00
    MSTORE
    PUSH 0x00
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
L29:    // JUMPDEST
    POP
    PUSH 0x44
    CALLDATASIZE
    LT
    ISZERO
    JUMPI L30
    PUSH 0x00
    PUSH 0x00
    REVERT
L30:    // JUMPDEST
    CALLVALUE
    ISZERO
    JUMPI L31
    PUSH 0x00
    PUSH 0x00
    REVERT
L31:    // JUMPDEST
    PUSH 0x04
    CALLDATALOAD
    PUSH 0x24
    CALLDATALOAD
    CALLER
    DUP1
    PUSH 0x00
    MSTORE
    PUSH 0x01
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
L32:    // JUMPDEST
    POP
    PUSH 0x04
    CALLDATASIZE
    LT
    ISZERO
    JUMPI L33
    PUSH 0x00
    PUSH 0x00
    REVERT
L33:    // JUMPDEST
    CALLVALUE
    ISZERO
    JUMPI L34
    PUSH 0x00
    PUSH 0x00
    REVERT
L34:    // JUMPDEST
    PUSH 0x02
    SLOAD
    DUP1
    PUSH 0x80
    MSTORE
    PUSH 0x20
    PUSH 0x80
    RETURN
    POP
    JUMP L3
L35:    // JUMPDEST
    POP
    PUSH 0x24
    CALLDATASIZE
    LT
    ISZERO
    JUMPI L36
    PUSH 0x00
    PUSH 0x00
    REVERT
L36:    // JUMPDEST
    CALLVALUE
    ISZERO
    JUMPI L37
    PUSH 0x00
    PUSH 0x00
    REVERT
L37:    // JUMPDEST
    PUSH 0x04
    CALLDATALOAD
    DUP1
    PUSH 0x00
    MSTORE
    PUSH 0x00
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
L38:    // JUMPDEST
    POP
    PUSH 0x44
    CALLDATASIZE
    LT
    ISZERO
    JUMPI L39
    PUSH 0x00
    PUSH 0x00
    REVERT
L39:    // JUMPDEST
    CALLVALUE
    ISZERO
    JUMPI L40
    PUSH 0x00
    PUSH 0x00
    REVERT
L40:    // JUMPDEST
    PUSH 0x04
    CALLDATALOAD
    PUSH 0x24
    CALLDATALOAD
    DUP2
    PUSH 0x00
    MSTORE
    PUSH 0x01
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
L3:    // JUMPDEST
