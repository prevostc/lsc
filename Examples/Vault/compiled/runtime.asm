// Labelled pre-assembly (powdr YulEvmCompiler.Asm, before lowerProg).
// Each `Ln:` is a JUMPDEST. JUMP/JUMPI take labels, not byte offsets.
// selector → function  (hex and decimal; `switch` cases print decimal)
//   0xb6b55f25  (3065339685)  deposit(uint256)
//   0x2e1a7d4d  (773487949)  withdraw(uint256)
//   0xef8b30f7  (4018876663)  previewDeposit(uint256)
//   0x4cdad506  (1289409798)  previewRedeem(uint256)
//   0x8456cb59  (2220280665)  pause()
//   0x3f4ba83a  (1061922874)  unpause()
//   0x67dda112  (1742577938)  paused?()
//   0x313ce567  (826074471)  decimals()

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
    JUMPI L25
    DUP1
    PUSH 0xef8b30f7    // selector: previewDeposit(uint256)
    EQ
    JUMPI L39
    DUP1
    PUSH 0x4cdad506    // selector: previewRedeem(uint256)
    EQ
    JUMPI L45
    DUP1
    PUSH 0x8456cb59    // selector: pause()
    EQ
    JUMPI L49
    DUP1
    PUSH 0x3f4ba83a    // selector: unpause()
    EQ
    JUMPI L52
    DUP1
    PUSH 0x67dda112    // selector: paused?()
    EQ
    JUMPI L55
    DUP1
    PUSH 0x313ce567    // selector: decimals()
    EQ
    JUMPI L57
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
    PUSH 0x03
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
    PUSH 0x01
    SLOAD
    PUSH 0x00
    DUP2
    EQ
    DUP1
    PUSH 0x00
    EQ
    JUMPI L8
    POP
    DUP6
    DUP1
    PUSH 0x00
    LT
    JUMPI L18
    PUSH 0x9811e0c7    // selector: ZeroShares()
    PUSH 0xe0
    SHL
    PUSH 0x80
    MSTORE
    PUSH 0x04
    PUSH 0x80
    REVERT
L18:    // JUMPDEST
    PUSH 0x00
    PUSH 0x05
    SLOAD
    PUSH 0x23b872dd
    PUSH 0xe0
    SHL
    PUSH 0x80
    MSTORE
    DUP7
    PUSH 0x84
    MSTORE
    DUP6
    PUSH 0xa4
    MSTORE
    DUP9
    PUSH 0xc4
    MSTORE
    PUSH 0x20
    PUSH 0x80
    PUSH 0x64
    PUSH 0x80
    PUSH 0x00
    DUP6
    PUSH 0x0f4240
    CALL
    DUP1
    JUMPI L19
    PUSH 0x00
    PUSH 0x00
    REVERT
L19:    // JUMPDEST
    PUSH 0x01
    PUSH 0x80
    MLOAD
    EQ
    PUSH 0x20
    RETURNDATASIZE
    LT
    ISZERO
    AND
    RETURNDATASIZE
    ISZERO
    OR
    JUMPI L20
    PUSH 0x00
    PUSH 0x00
    REVERT
L20:    // JUMPDEST
    PUSH 0x01
    SWAP3
    POP
    POP
    POP
    PUSH 0x00
    DUP2
    EQ
    ISZERO
    JUMPI L21
    PUSH 0x90b8ec18    // selector: TransferFailed()
    PUSH 0xe0
    SHL
    PUSH 0x80
    MSTORE
    PUSH 0x04
    PUSH 0x80
    REVERT
L21:    // JUMPDEST
    DUP8
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
    PUSH 0x00
    SSTORE
    DUP4
    DUP4
    ADD
    DUP4
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
    DUP1
    PUSH 0x01
    SSTORE
    DUP8
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
    DUP6
    ADD
    DUP6
    DUP2
    LT
    ISZERO
    JUMPI L24
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
L24:    // JUMPDEST
    DUP10
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
    DUP12
    PUSH 0xa0
    MSTORE
    DUP6
    PUSH 0xc0
    MSTORE
    PUSH 0x90890809c654f11d6e72a28fa60149770a0d11ec6c92319d6ceb2bb0a4ea1a15    // topic: Deposit(address,uint256,uint256)
    PUSH 0x60
    PUSH 0x80
    LOG1
    DUP6
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
    JUMP L7
L8:    // JUMPDEST
    POP
    DUP2
    JUMPI L9
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
L9:    // JUMPDEST
    DUP6
    DUP2
    MUL
    DUP7
    DUP3
    DUP3
    DIV
    EQ
    DUP3
    ISZERO
    OR
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
    DUP3
    DUP2
    DIV
    SWAP1
    POP
    DUP1
    PUSH 0x00
    LT
    JUMPI L11
    PUSH 0x9811e0c7    // selector: ZeroShares()
    PUSH 0xe0
    SHL
    PUSH 0x80
    MSTORE
    PUSH 0x04
    PUSH 0x80
    REVERT
L11:    // JUMPDEST
    PUSH 0x00
    PUSH 0x05
    SLOAD
    PUSH 0x23b872dd
    PUSH 0xe0
    SHL
    PUSH 0x80
    MSTORE
    DUP7
    PUSH 0x84
    MSTORE
    DUP6
    PUSH 0xa4
    MSTORE
    DUP9
    PUSH 0xc4
    MSTORE
    PUSH 0x20
    PUSH 0x80
    PUSH 0x64
    PUSH 0x80
    PUSH 0x00
    DUP6
    PUSH 0x0f4240
    CALL
    DUP1
    JUMPI L12
    PUSH 0x00
    PUSH 0x00
    REVERT
L12:    // JUMPDEST
    PUSH 0x01
    PUSH 0x80
    MLOAD
    EQ
    PUSH 0x20
    RETURNDATASIZE
    LT
    ISZERO
    AND
    RETURNDATASIZE
    ISZERO
    OR
    JUMPI L13
    PUSH 0x00
    PUSH 0x00
    REVERT
L13:    // JUMPDEST
    PUSH 0x01
    SWAP3
    POP
    POP
    POP
    PUSH 0x00
    DUP2
    EQ
    ISZERO
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
    DUP8
    DUP5
    ADD
    DUP5
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
    DUP1
    PUSH 0x00
    SSTORE
    DUP4
    DUP4
    ADD
    DUP4
    DUP2
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
    DUP1
    PUSH 0x01
    SSTORE
    DUP8
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
    DUP6
    ADD
    DUP6
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
    DUP10
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
    DUP12
    PUSH 0xa0
    MSTORE
    DUP6
    PUSH 0xc0
    MSTORE
    PUSH 0x90890809c654f11d6e72a28fa60149770a0d11ec6c92319d6ceb2bb0a4ea1a15    // topic: Deposit(address,uint256,uint256)
    PUSH 0x60
    PUSH 0x80
    LOG1
    DUP6
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
L7:    // JUMPDEST
    POP
    POP
    POP
    POP
    POP
    POP
    JUMP L2
L25:    // JUMPDEST
    POP
    PUSH 0x24
    CALLDATASIZE
    LT
    ISZERO
    JUMPI L26
    PUSH 0x00
    PUSH 0x00
    REVERT
L26:    // JUMPDEST
    PUSH 0x04
    CALLDATALOAD
    PUSH 0x03
    SLOAD
    PUSH 0x00
    DUP2
    EQ
    JUMPI L27
    PUSH 0x9e87fac8    // selector: Paused()
    PUSH 0xe0
    SHL
    PUSH 0x80
    MSTORE
    PUSH 0x04
    PUSH 0x80
    REVERT
L27:    // JUMPDEST
    DUP2
    PUSH 0x00
    LT
    JUMPI L28
    PUSH 0xf4560403    // selector: Zero()
    PUSH 0xe0
    SHL
    PUSH 0x80
    MSTORE
    PUSH 0x04
    PUSH 0x80
    REVERT
L28:    // JUMPDEST
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
    DUP4
    DUP2
    LT
    ISZERO
    JUMPI L29
    PUSH 0x39996567    // selector: InsufficientShares()
    PUSH 0xe0
    SHL
    PUSH 0x80
    MSTORE
    PUSH 0x04
    PUSH 0x80
    REVERT
L29:    // JUMPDEST
    PUSH 0x00
    SLOAD
    PUSH 0x01
    SLOAD
    DUP1
    JUMPI L30
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
L30:    // JUMPDEST
    DUP6
    DUP3
    MUL
    DUP7
    DUP4
    DUP3
    DIV
    EQ
    DUP4
    ISZERO
    OR
    JUMPI L31
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
L31:    // JUMPDEST
    DUP2
    DUP2
    DIV
    SWAP1
    POP
    DUP1
    PUSH 0x00
    LT
    JUMPI L32
    PUSH 0x32d971dc    // selector: ZeroAssets()
    PUSH 0xe0
    SHL
    PUSH 0x80
    MSTORE
    PUSH 0x04
    PUSH 0x80
    REVERT
L32:    // JUMPDEST
    DUP7
    DUP5
    LT
    ISZERO
    JUMPI L33
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
L33:    // JUMPDEST
    DUP7
    DUP5
    SUB
    DUP6
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
    DUP8
    DUP4
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
    DUP8
    DUP4
    SUB
    DUP1
    PUSH 0x01
    SSTORE
    DUP3
    DUP6
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
    DUP3
    DUP6
    SUB
    DUP1
    PUSH 0x00
    SSTORE
    PUSH 0x00
    PUSH 0x05
    SLOAD
    PUSH 0xa9059cbb
    PUSH 0xe0
    SHL
    PUSH 0x80
    MSTORE
    DUP10
    PUSH 0x84
    MSTORE
    DUP6
    PUSH 0xa4
    MSTORE
    PUSH 0x20
    PUSH 0x80
    PUSH 0x44
    PUSH 0x80
    PUSH 0x00
    DUP6
    PUSH 0x0f4240
    CALL
    DUP1
    JUMPI L36
    PUSH 0x00
    PUSH 0x00
    REVERT
L36:    // JUMPDEST
    PUSH 0x01
    PUSH 0x80
    MLOAD
    EQ
    PUSH 0x20
    RETURNDATASIZE
    LT
    ISZERO
    AND
    RETURNDATASIZE
    ISZERO
    OR
    JUMPI L37
    PUSH 0x00
    PUSH 0x00
    REVERT
L37:    // JUMPDEST
    PUSH 0x01
    SWAP3
    POP
    POP
    POP
    PUSH 0x00
    DUP2
    EQ
    ISZERO
    JUMPI L38
    PUSH 0x90b8ec18    // selector: TransferFailed()
    PUSH 0xe0
    SHL
    PUSH 0x80
    MSTORE
    PUSH 0x04
    PUSH 0x80
    REVERT
L38:    // JUMPDEST
    DUP9
    PUSH 0x80
    MSTORE
    DUP5
    PUSH 0xa0
    MSTORE
    DUP11
    PUSH 0xc0
    MSTORE
    PUSH 0xf279e6a1f5e320cca91135676d9cb6e44ca8a08c0b88342bcdb1144f6511b568    // topic: Withdraw(address,uint256,uint256)
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
    POP
    POP
    POP
    POP
    POP
    POP
    JUMP L2
L39:    // JUMPDEST
    POP
    PUSH 0x24
    CALLDATASIZE
    LT
    ISZERO
    JUMPI L40
    PUSH 0x00
    PUSH 0x00
    REVERT
L40:    // JUMPDEST
    PUSH 0x04
    CALLDATALOAD
    PUSH 0x00
    SLOAD
    PUSH 0x01
    SLOAD
    PUSH 0x00
    DUP2
    EQ
    DUP1
    PUSH 0x00
    EQ
    JUMPI L42
    POP
    DUP3
    PUSH 0x80
    MSTORE
    PUSH 0x20
    PUSH 0x80
    RETURN
    JUMP L41
L42:    // JUMPDEST
    POP
    DUP2
    JUMPI L43
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
L43:    // JUMPDEST
    DUP3
    DUP2
    MUL
    DUP4
    DUP3
    DUP3
    DIV
    EQ
    DUP3
    ISZERO
    OR
    JUMPI L44
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
L44:    // JUMPDEST
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
L41:    // JUMPDEST
    POP
    POP
    POP
    JUMP L2
L45:    // JUMPDEST
    POP
    PUSH 0x24
    CALLDATASIZE
    LT
    ISZERO
    JUMPI L46
    PUSH 0x00
    PUSH 0x00
    REVERT
L46:    // JUMPDEST
    PUSH 0x04
    CALLDATALOAD
    PUSH 0x00
    SLOAD
    PUSH 0x01
    SLOAD
    DUP1
    JUMPI L47
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
L47:    // JUMPDEST
    DUP3
    DUP3
    MUL
    DUP4
    DUP4
    DUP3
    DIV
    EQ
    DUP4
    ISZERO
    OR
    JUMPI L48
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
L48:    // JUMPDEST
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
    JUMP L2
L49:    // JUMPDEST
    POP
    PUSH 0x04
    CALLDATASIZE
    LT
    ISZERO
    JUMPI L50
    PUSH 0x00
    PUSH 0x00
    REVERT
L50:    // JUMPDEST
    CALLER
    PUSH 0x04
    SLOAD
    DUP1
    DUP3
    EQ
    JUMPI L51
    PUSH 0x30cd7471    // selector: NotOwner()
    PUSH 0xe0
    SHL
    PUSH 0x80
    MSTORE
    PUSH 0x04
    PUSH 0x80
    REVERT
L51:    // JUMPDEST
    PUSH 0x01
    PUSH 0x03
    SSTORE
    PUSH 0x9e87fac88ff661f02d44f95383c817fece4bce600a3dab7a54406878b965e752    // topic: Paused()
    PUSH 0x00
    PUSH 0x80
    LOG1
    STOP
    POP
    POP
    JUMP L2
L52:    // JUMPDEST
    POP
    PUSH 0x04
    CALLDATASIZE
    LT
    ISZERO
    JUMPI L53
    PUSH 0x00
    PUSH 0x00
    REVERT
L53:    // JUMPDEST
    CALLER
    PUSH 0x04
    SLOAD
    DUP1
    DUP3
    EQ
    JUMPI L54
    PUSH 0x30cd7471    // selector: NotOwner()
    PUSH 0xe0
    SHL
    PUSH 0x80
    MSTORE
    PUSH 0x04
    PUSH 0x80
    REVERT
L54:    // JUMPDEST
    PUSH 0x00
    PUSH 0x03
    SSTORE
    PUSH 0xa45f47fdea8a1efdd9029a5691c7f759c32b7c698632b563573e155625d16933    // topic: Unpaused()
    PUSH 0x00
    PUSH 0x80
    LOG1
    STOP
    POP
    POP
    JUMP L2
L55:    // JUMPDEST
    POP
    PUSH 0x04
    CALLDATASIZE
    LT
    ISZERO
    JUMPI L56
    PUSH 0x00
    PUSH 0x00
    REVERT
L56:    // JUMPDEST
    PUSH 0x03
    SLOAD
    DUP1
    PUSH 0x80
    MSTORE
    PUSH 0x20
    PUSH 0x80
    RETURN
    POP
    JUMP L2
L57:    // JUMPDEST
    POP
    PUSH 0x04
    CALLDATASIZE
    LT
    ISZERO
    JUMPI L58
    PUSH 0x00
    PUSH 0x00
    REVERT
L58:    // JUMPDEST
    PUSH 0x06
    SLOAD
    DUP1
    PUSH 0x80
    MSTORE
    PUSH 0x20
    PUSH 0x80
    RETURN
    POP
L2:    // JUMPDEST
