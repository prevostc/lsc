// Labelled pre-assembly (powdr YulEvmCompiler.Asm, before lowerProg).
// Each `Ln:` is a JUMPDEST. JUMP/JUMPI take labels, not byte offsets.
// selector → function  (hex and decimal; `switch` cases print decimal)
//   0xb6b55f25  (3065339685)  deposit(uint256)
//   0x2e1a7d4d  (773487949)  withdraw(uint256)
//   0xef8b30f7  (4018876663)  previewDeposit(uint256)
//   0x4cdad506  (1289409798)  previewRedeem(uint256)
//   0x8456cb59  (2220280665)  pause()
//   0x3f4ba83a  (1061922874)  unpause()
//   0xb187bd26  (2978463014)  isPaused()

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
    PUSH 0xb6b55f25    // selector: deposit(uint256)
    EQ
    JUMPI L3
    DUP1
    PUSH 0x2e1a7d4d    // selector: withdraw(uint256)
    EQ
    JUMPI L27
    DUP1
    PUSH 0xef8b30f7    // selector: previewDeposit(uint256)
    EQ
    JUMPI L42
    DUP1
    PUSH 0x4cdad506    // selector: previewRedeem(uint256)
    EQ
    JUMPI L52
    DUP1
    PUSH 0x8456cb59    // selector: pause()
    EQ
    JUMPI L58
    DUP1
    PUSH 0x3f4ba83a    // selector: unpause()
    EQ
    JUMPI L61
    DUP1
    PUSH 0xb187bd26    // selector: isPaused()
    EQ
    JUMPI L64
    POP
    PUSH 0x00
    PUSH 0x00
    REVERT
    JUMP L2
L3:    // JUMPDEST
    POP
    PUSH 0x24
    CALLDATASIZE
    LT
    ISZERO
    JUMPI L4
    PUSH 0x00
    PUSH 0x00
    REVERT
L4:    // JUMPDEST
    PUSH 0x04
    CALLDATALOAD
    PUSH 0x02
    SLOAD
    PUSH 0x00
    DUP2
    EQ
    JUMPI L5
    PUSH 0x9e87fac8    // selector: Paused()
    PUSH 0xe0
    SHL
    PUSH 0x80
    MSTORE
    PUSH 0x04
    PUSH 0x80
    REVERT
L5:    // JUMPDEST
    DUP2
    PUSH 0x00
    LT
    JUMPI L6
    PUSH 0xf4560403    // selector: Zero()
    PUSH 0xe0
    SHL
    PUSH 0x80
    MSTORE
    PUSH 0x04
    PUSH 0x80
    REVERT
L6:    // JUMPDEST
    CALLER
    ADDRESS
    PUSH 0x00
    SLOAD
    PUSH 0x00
    PUSH 0x70a08231
    PUSH 0xe0
    SHL
    PUSH 0x80
    MSTORE
    DUP3
    PUSH 0x84
    MSTORE
    PUSH 0x20
    PUSH 0x80
    PUSH 0x24
    PUSH 0x80
    DUP6
    PUSH 0x0f4240
    STATICCALL
    DUP1
    JUMPI L7
    PUSH 0x00
    PUSH 0x00
    REVERT
L7:    // JUMPDEST
    PUSH 0x40
    RETURNDATASIZE
    LT
    PUSH 0x20
    RETURNDATASIZE
    LT
    ISZERO
    AND
    JUMPI L8
    PUSH 0x00
    PUSH 0x00
    REVERT
L8:    // JUMPDEST
    PUSH 0x80
    MLOAD
    SWAP2
    POP
    POP
    PUSH 0x03
    SLOAD
    PUSH 0x01
    PUSH 0x01
    PUSH 0x00
    DUP4
    EQ
    DUP1
    PUSH 0x00
    EQ
    JUMPI L10
    POP
    DUP2
    JUMPI L19
    PUSH 0x4e487b71
    PUSH 0xe0
    SHL
    PUSH 0x80
    MSTORE
    PUSH 0x12
    PUSH 0x84
    MSTORE
    PUSH 0x24
    PUSH 0x80
    REVERT
L19:    // JUMPDEST
    DUP9
    DUP2
    MUL
    DUP10
    DUP3
    DUP3
    DIV
    EQ
    DUP3
    ISZERO
    OR
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
    DUP3
    DUP2
    DIV
    SWAP1
    POP
    DUP1
    PUSH 0x00
    LT
    JUMPI L21
    PUSH 0x9811e0c7    // selector: ZeroShares()
    PUSH 0xe0
    SHL
    PUSH 0x80
    MSTORE
    PUSH 0x04
    PUSH 0x80
    REVERT
L21:    // JUMPDEST
    DUP1
    DUP5
    ADD
    DUP5
    DUP2
    LT
    ISZERO
    JUMPI L22
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
L22:    // JUMPDEST
    DUP1
    PUSH 0x03
    SSTORE
    DUP9
    PUSH 0x00
    MSTORE
    PUSH 0x04
    PUSH 0x20
    MSTORE
    PUSH 0x40
    PUSH 0x00
    KECCAK256
    SLOAD
    DUP3
    DUP2
    ADD
    DUP2
    DUP2
    LT
    ISZERO
    JUMPI L23
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
L23:    // JUMPDEST
    DUP11
    PUSH 0x00
    MSTORE
    PUSH 0x04
    PUSH 0x20
    MSTORE
    DUP1
    PUSH 0x40
    PUSH 0x00
    KECCAK256
    SSTORE
    PUSH 0x00
    PUSH 0x23b872dd
    PUSH 0xe0
    SHL
    PUSH 0x80
    MSTORE
    DUP12
    PUSH 0x84
    MSTORE
    DUP11
    PUSH 0xa4
    MSTORE
    DUP14
    PUSH 0xc4
    MSTORE
    PUSH 0x20
    PUSH 0x80
    PUSH 0x64
    PUSH 0x80
    PUSH 0x00
    DUP15
    PUSH 0x0f4240
    CALL
    DUP1
    JUMPI L24
    PUSH 0x00
    PUSH 0x00
    REVERT
L24:    // JUMPDEST
    PUSH 0x40
    RETURNDATASIZE
    LT
    PUSH 0x20
    RETURNDATASIZE
    LT
    ISZERO
    AND
    RETURNDATASIZE
    ISZERO
    OR
    JUMPI L25
    PUSH 0x00
    PUSH 0x00
    REVERT
L25:    // JUMPDEST
    PUSH 0x80
    MLOAD
    ISZERO
    ISZERO
    RETURNDATASIZE
    ISZERO
    OR
    SWAP2
    POP
    POP
    PUSH 0x01
    DUP2
    EQ
    JUMPI L26
    PUSH 0x90b8ec18    // selector: TransferFailed()
    PUSH 0xe0
    SHL
    PUSH 0x80
    MSTORE
    PUSH 0x04
    PUSH 0x80
    REVERT
L26:    // JUMPDEST
    DUP12
    PUSH 0x80
    MSTORE
    DUP14
    PUSH 0xa0
    MSTORE
    DUP5
    PUSH 0xc0
    MSTORE
    PUSH 0x90890809c654f11d6e72a28fa60149770a0d11ec6c92319d6ceb2bb0a4ea1a15    // topic: Deposit(address,uint256,uint256)
    PUSH 0x60
    PUSH 0x80
    LOG1
    DUP5
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
    JUMP L9
L10:    // JUMPDEST
    POP
    DUP4
    JUMPI L11
    PUSH 0x4e487b71
    PUSH 0xe0
    SHL
    PUSH 0x80
    MSTORE
    PUSH 0x12
    PUSH 0x84
    MSTORE
    PUSH 0x24
    PUSH 0x80
    REVERT
L11:    // JUMPDEST
    DUP9
    DUP4
    MUL
    DUP10
    DUP5
    DUP3
    DIV
    EQ
    DUP5
    ISZERO
    OR
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
    DUP5
    DUP2
    DIV
    SWAP1
    POP
    DUP1
    PUSH 0x00
    LT
    JUMPI L13
    PUSH 0x9811e0c7    // selector: ZeroShares()
    PUSH 0xe0
    SHL
    PUSH 0x80
    MSTORE
    PUSH 0x04
    PUSH 0x80
    REVERT
L13:    // JUMPDEST
    DUP1
    DUP5
    ADD
    DUP5
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
    DUP1
    PUSH 0x03
    SSTORE
    DUP9
    PUSH 0x00
    MSTORE
    PUSH 0x04
    PUSH 0x20
    MSTORE
    PUSH 0x40
    PUSH 0x00
    KECCAK256
    SLOAD
    DUP3
    DUP2
    ADD
    DUP2
    DUP2
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
    DUP11
    PUSH 0x00
    MSTORE
    PUSH 0x04
    PUSH 0x20
    MSTORE
    DUP1
    PUSH 0x40
    PUSH 0x00
    KECCAK256
    SSTORE
    PUSH 0x00
    PUSH 0x23b872dd
    PUSH 0xe0
    SHL
    PUSH 0x80
    MSTORE
    DUP12
    PUSH 0x84
    MSTORE
    DUP11
    PUSH 0xa4
    MSTORE
    DUP14
    PUSH 0xc4
    MSTORE
    PUSH 0x20
    PUSH 0x80
    PUSH 0x64
    PUSH 0x80
    PUSH 0x00
    DUP15
    PUSH 0x0f4240
    CALL
    DUP1
    JUMPI L16
    PUSH 0x00
    PUSH 0x00
    REVERT
L16:    // JUMPDEST
    PUSH 0x40
    RETURNDATASIZE
    LT
    PUSH 0x20
    RETURNDATASIZE
    LT
    ISZERO
    AND
    RETURNDATASIZE
    ISZERO
    OR
    JUMPI L17
    PUSH 0x00
    PUSH 0x00
    REVERT
L17:    // JUMPDEST
    PUSH 0x80
    MLOAD
    ISZERO
    ISZERO
    RETURNDATASIZE
    ISZERO
    OR
    SWAP2
    POP
    POP
    PUSH 0x01
    DUP2
    EQ
    JUMPI L18
    PUSH 0x90b8ec18    // selector: TransferFailed()
    PUSH 0xe0
    SHL
    PUSH 0x80
    MSTORE
    PUSH 0x04
    PUSH 0x80
    REVERT
L18:    // JUMPDEST
    DUP12
    PUSH 0x80
    MSTORE
    DUP14
    PUSH 0xa0
    MSTORE
    DUP5
    PUSH 0xc0
    MSTORE
    PUSH 0x90890809c654f11d6e72a28fa60149770a0d11ec6c92319d6ceb2bb0a4ea1a15    // topic: Deposit(address,uint256,uint256)
    PUSH 0x60
    PUSH 0x80
    LOG1
    DUP5
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
L9:    // JUMPDEST
    POP
    POP
    POP
    POP
    POP
    POP
    POP
    POP
    POP
    JUMP L2
L27:    // JUMPDEST
    POP
    PUSH 0x24
    CALLDATASIZE
    LT
    ISZERO
    JUMPI L28
    PUSH 0x00
    PUSH 0x00
    REVERT
L28:    // JUMPDEST
    PUSH 0x04
    CALLDATALOAD
    PUSH 0x02
    SLOAD
    PUSH 0x00
    DUP2
    EQ
    JUMPI L29
    PUSH 0x9e87fac8    // selector: Paused()
    PUSH 0xe0
    SHL
    PUSH 0x80
    MSTORE
    PUSH 0x04
    PUSH 0x80
    REVERT
L29:    // JUMPDEST
    DUP2
    PUSH 0x00
    LT
    JUMPI L30
    PUSH 0xf4560403    // selector: Zero()
    PUSH 0xe0
    SHL
    PUSH 0x80
    MSTORE
    PUSH 0x04
    PUSH 0x80
    REVERT
L30:    // JUMPDEST
    CALLER
    DUP1
    PUSH 0x00
    MSTORE
    PUSH 0x04
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
    JUMPI L31
    PUSH 0x39996567    // selector: InsufficientShares()
    PUSH 0xe0
    SHL
    PUSH 0x80
    MSTORE
    PUSH 0x04
    PUSH 0x80
    REVERT
L31:    // JUMPDEST
    ADDRESS
    PUSH 0x00
    SLOAD
    PUSH 0x00
    PUSH 0x70a08231
    PUSH 0xe0
    SHL
    PUSH 0x80
    MSTORE
    DUP3
    PUSH 0x84
    MSTORE
    PUSH 0x20
    PUSH 0x80
    PUSH 0x24
    PUSH 0x80
    DUP6
    PUSH 0x0f4240
    STATICCALL
    DUP1
    JUMPI L32
    PUSH 0x00
    PUSH 0x00
    REVERT
L32:    // JUMPDEST
    PUSH 0x40
    RETURNDATASIZE
    LT
    PUSH 0x20
    RETURNDATASIZE
    LT
    ISZERO
    AND
    JUMPI L33
    PUSH 0x00
    PUSH 0x00
    REVERT
L33:    // JUMPDEST
    PUSH 0x80
    MLOAD
    SWAP2
    POP
    POP
    PUSH 0x03
    SLOAD
    DUP1
    JUMPI L34
    PUSH 0x4e487b71
    PUSH 0xe0
    SHL
    PUSH 0x80
    MSTORE
    PUSH 0x12
    PUSH 0x84
    MSTORE
    PUSH 0x24
    PUSH 0x80
    REVERT
L34:    // JUMPDEST
    DUP8
    DUP3
    MUL
    DUP9
    DUP4
    DUP3
    DIV
    EQ
    DUP4
    ISZERO
    OR
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
    DUP2
    DUP2
    DIV
    SWAP1
    POP
    DUP1
    PUSH 0x00
    LT
    JUMPI L36
    PUSH 0x32d971dc    // selector: ZeroAssets()
    PUSH 0xe0
    SHL
    PUSH 0x80
    MSTORE
    PUSH 0x04
    PUSH 0x80
    REVERT
L36:    // JUMPDEST
    DUP9
    DUP7
    LT
    ISZERO
    JUMPI L37
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
L37:    // JUMPDEST
    DUP9
    DUP7
    SUB
    DUP8
    PUSH 0x00
    MSTORE
    PUSH 0x04
    PUSH 0x20
    MSTORE
    DUP1
    PUSH 0x40
    PUSH 0x00
    KECCAK256
    SSTORE
    DUP10
    DUP4
    LT
    ISZERO
    JUMPI L38
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
L38:    // JUMPDEST
    DUP10
    DUP4
    SUB
    DUP1
    PUSH 0x03
    SSTORE
    PUSH 0x00
    PUSH 0xa9059cbb
    PUSH 0xe0
    SHL
    PUSH 0x80
    MSTORE
    DUP10
    PUSH 0x84
    MSTORE
    DUP4
    PUSH 0xa4
    MSTORE
    PUSH 0x20
    PUSH 0x80
    PUSH 0x44
    PUSH 0x80
    PUSH 0x00
    DUP12
    PUSH 0x0f4240
    CALL
    DUP1
    JUMPI L39
    PUSH 0x00
    PUSH 0x00
    REVERT
L39:    // JUMPDEST
    PUSH 0x40
    RETURNDATASIZE
    LT
    PUSH 0x20
    RETURNDATASIZE
    LT
    ISZERO
    AND
    RETURNDATASIZE
    ISZERO
    OR
    JUMPI L40
    PUSH 0x00
    PUSH 0x00
    REVERT
L40:    // JUMPDEST
    PUSH 0x80
    MLOAD
    ISZERO
    ISZERO
    RETURNDATASIZE
    ISZERO
    OR
    SWAP2
    POP
    POP
    PUSH 0x01
    DUP2
    EQ
    JUMPI L41
    PUSH 0x90b8ec18    // selector: TransferFailed()
    PUSH 0xe0
    SHL
    PUSH 0x80
    MSTORE
    PUSH 0x04
    PUSH 0x80
    REVERT
L41:    // JUMPDEST
    DUP10
    PUSH 0x80
    MSTORE
    DUP4
    PUSH 0xa0
    MSTORE
    DUP12
    PUSH 0xc0
    MSTORE
    PUSH 0xf279e6a1f5e320cca91135676d9cb6e44ca8a08c0b88342bcdb1144f6511b568    // topic: Withdraw(address,uint256,uint256)
    PUSH 0x60
    PUSH 0x80
    LOG1
    DUP4
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
    POP
    POP
    JUMP L2
L42:    // JUMPDEST
    POP
    PUSH 0x24
    CALLDATASIZE
    LT
    ISZERO
    JUMPI L43
    PUSH 0x00
    PUSH 0x00
    REVERT
L43:    // JUMPDEST
    PUSH 0x04
    CALLDATALOAD
    ADDRESS
    PUSH 0x00
    SLOAD
    PUSH 0x00
    PUSH 0x70a08231
    PUSH 0xe0
    SHL
    PUSH 0x80
    MSTORE
    DUP3
    PUSH 0x84
    MSTORE
    PUSH 0x20
    PUSH 0x80
    PUSH 0x24
    PUSH 0x80
    DUP6
    PUSH 0x0f4240
    STATICCALL
    DUP1
    JUMPI L44
    PUSH 0x00
    PUSH 0x00
    REVERT
L44:    // JUMPDEST
    PUSH 0x40
    RETURNDATASIZE
    LT
    PUSH 0x20
    RETURNDATASIZE
    LT
    ISZERO
    AND
    JUMPI L45
    PUSH 0x00
    PUSH 0x00
    REVERT
L45:    // JUMPDEST
    PUSH 0x80
    MLOAD
    SWAP2
    POP
    POP
    PUSH 0x03
    SLOAD
    PUSH 0x01
    PUSH 0x01
    PUSH 0x00
    DUP4
    EQ
    DUP1
    PUSH 0x00
    EQ
    JUMPI L47
    POP
    DUP2
    JUMPI L50
    PUSH 0x4e487b71
    PUSH 0xe0
    SHL
    PUSH 0x80
    MSTORE
    PUSH 0x12
    PUSH 0x84
    MSTORE
    PUSH 0x24
    PUSH 0x80
    REVERT
L50:    // JUMPDEST
    DUP7
    DUP2
    MUL
    DUP8
    DUP3
    DUP3
    DIV
    EQ
    DUP3
    ISZERO
    OR
    JUMPI L51
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
L51:    // JUMPDEST
    DUP3
    DUP2
    DIV
    SWAP1
    POP
    DUP1
    PUSH 0x80
    MSTORE
    PUSH 0x20
    PUSH 0x80
    RETURN
    POP
    JUMP L46
L47:    // JUMPDEST
    POP
    DUP4
    JUMPI L48
    PUSH 0x4e487b71
    PUSH 0xe0
    SHL
    PUSH 0x80
    MSTORE
    PUSH 0x12
    PUSH 0x84
    MSTORE
    PUSH 0x24
    PUSH 0x80
    REVERT
L48:    // JUMPDEST
    DUP7
    DUP4
    MUL
    DUP8
    DUP5
    DUP3
    DIV
    EQ
    DUP5
    ISZERO
    OR
    JUMPI L49
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
L49:    // JUMPDEST
    DUP5
    DUP2
    DIV
    SWAP1
    POP
    DUP1
    PUSH 0x80
    MSTORE
    PUSH 0x20
    PUSH 0x80
    RETURN
    POP
L46:    // JUMPDEST
    POP
    POP
    POP
    POP
    POP
    POP
    POP
    JUMP L2
L52:    // JUMPDEST
    POP
    PUSH 0x24
    CALLDATASIZE
    LT
    ISZERO
    JUMPI L53
    PUSH 0x00
    PUSH 0x00
    REVERT
L53:    // JUMPDEST
    PUSH 0x04
    CALLDATALOAD
    ADDRESS
    PUSH 0x00
    SLOAD
    PUSH 0x00
    PUSH 0x70a08231
    PUSH 0xe0
    SHL
    PUSH 0x80
    MSTORE
    DUP3
    PUSH 0x84
    MSTORE
    PUSH 0x20
    PUSH 0x80
    PUSH 0x24
    PUSH 0x80
    DUP6
    PUSH 0x0f4240
    STATICCALL
    DUP1
    JUMPI L54
    PUSH 0x00
    PUSH 0x00
    REVERT
L54:    // JUMPDEST
    PUSH 0x40
    RETURNDATASIZE
    LT
    PUSH 0x20
    RETURNDATASIZE
    LT
    ISZERO
    AND
    JUMPI L55
    PUSH 0x00
    PUSH 0x00
    REVERT
L55:    // JUMPDEST
    PUSH 0x80
    MLOAD
    SWAP2
    POP
    POP
    PUSH 0x03
    SLOAD
    DUP1
    JUMPI L56
    PUSH 0x4e487b71
    PUSH 0xe0
    SHL
    PUSH 0x80
    MSTORE
    PUSH 0x12
    PUSH 0x84
    MSTORE
    PUSH 0x24
    PUSH 0x80
    REVERT
L56:    // JUMPDEST
    DUP5
    DUP3
    MUL
    DUP6
    DUP4
    DUP3
    DIV
    EQ
    DUP4
    ISZERO
    OR
    JUMPI L57
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
L57:    // JUMPDEST
    DUP2
    DUP2
    DIV
    SWAP1
    POP
    DUP1
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
    JUMP L2
L58:    // JUMPDEST
    POP
    PUSH 0x04
    CALLDATASIZE
    LT
    ISZERO
    JUMPI L59
    PUSH 0x00
    PUSH 0x00
    REVERT
L59:    // JUMPDEST
    CALLER
    PUSH 0x01
    SLOAD
    DUP1
    DUP3
    EQ
    JUMPI L60
    PUSH 0x30cd7471    // selector: NotOwner()
    PUSH 0xe0
    SHL
    PUSH 0x80
    MSTORE
    PUSH 0x04
    PUSH 0x80
    REVERT
L60:    // JUMPDEST
    PUSH 0x01
    PUSH 0x02
    SSTORE
    PUSH 0x9e87fac88ff661f02d44f95383c817fece4bce600a3dab7a54406878b965e752    // topic: Paused()
    PUSH 0x00
    PUSH 0x80
    LOG1
    STOP
    POP
    POP
    JUMP L2
L61:    // JUMPDEST
    POP
    PUSH 0x04
    CALLDATASIZE
    LT
    ISZERO
    JUMPI L62
    PUSH 0x00
    PUSH 0x00
    REVERT
L62:    // JUMPDEST
    CALLER
    PUSH 0x01
    SLOAD
    DUP1
    DUP3
    EQ
    JUMPI L63
    PUSH 0x30cd7471    // selector: NotOwner()
    PUSH 0xe0
    SHL
    PUSH 0x80
    MSTORE
    PUSH 0x04
    PUSH 0x80
    REVERT
L63:    // JUMPDEST
    PUSH 0x00
    PUSH 0x02
    SSTORE
    PUSH 0xa45f47fdea8a1efdd9029a5691c7f759c32b7c698632b563573e155625d16933    // topic: Unpaused()
    PUSH 0x00
    PUSH 0x80
    LOG1
    STOP
    POP
    POP
    JUMP L2
L64:    // JUMPDEST
    POP
    PUSH 0x04
    CALLDATASIZE
    LT
    ISZERO
    JUMPI L65
    PUSH 0x00
    PUSH 0x00
    REVERT
L65:    // JUMPDEST
    PUSH 0x02
    SLOAD
    DUP1
    PUSH 0x80
    MSTORE
    PUSH 0x20
    PUSH 0x80
    RETURN
    POP
L2:    // JUMPDEST
