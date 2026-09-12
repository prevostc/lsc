// Labelled pre-assembly (powdr YulEvmCompiler.Asm, before lowerProg).
// Each `Ln:` is a JUMPDEST. JUMP/JUMPI take labels, not byte offsets.
// selector → function  (hex and decimal; `switch` cases print decimal)
//   0x9cd441da  (2631156186)  addLiquidity(uint256,uint256)
//   0x9c8f9f23  (2626658083)  removeLiquidity(uint256)
//   0x2b1087f0  (722503664)  swap0for1(uint256,uint256)
//   0x21d2da23  (567466531)  swap1for0(uint256,uint256)
//   0xce9c0bb7  (3466333111)  setProtocolShare(uint256)
//   0xf46901ed  (4100522477)  setFeeTo(address)
//   0xa1af5b9a  (2712624026)  collectProtocolFees()
//   0x0902f1ac  (151187884)  getReserves()
//   0xf5eb42dc  (4125835996)  sharesOf(address)
//   0x1ad8b03b  (450408507)  protocolFees()

    PUSH 0x0140
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
    PUSH 0x9cd441da    // selector: addLiquidity(uint256,uint256)
    EQ
    JUMPI L3
    DUP1
    PUSH 0x9c8f9f23    // selector: removeLiquidity(uint256)
    EQ
    JUMPI L50
    DUP1
    PUSH 0x2b1087f0    // selector: swap0for1(uint256,uint256)
    EQ
    JUMPI L71
    DUP1
    PUSH 0x21d2da23    // selector: swap1for0(uint256,uint256)
    EQ
    JUMPI L115
    DUP1
    PUSH 0xce9c0bb7    // selector: setProtocolShare(uint256)
    EQ
    JUMPI L159
    DUP1
    PUSH 0xf46901ed    // selector: setFeeTo(address)
    EQ
    JUMPI L163
    DUP1
    PUSH 0xa1af5b9a    // selector: collectProtocolFees()
    EQ
    JUMPI L166
    DUP1
    PUSH 0x0902f1ac    // selector: getReserves()
    EQ
    JUMPI L176
    DUP1
    PUSH 0xf5eb42dc    // selector: sharesOf(address)
    EQ
    JUMPI L178
    DUP1
    PUSH 0x1ad8b03b    // selector: protocolFees()
    EQ
    JUMPI L180
    POP
    PUSH 0x00
    PUSH 0x00
    REVERT
    JUMP L2
L3:    // JUMPDEST
    POP
    PUSH 0x44
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
    PUSH 0x0100
    MSTORE
    PUSH 0x24
    CALLDATALOAD
    PUSH 0x0120
    MSTORE
    PUSH 0x0100
    MLOAD
    PUSH 0x00
    LT
    JUMPI L5
    PUSH 0xf4560403    // selector: Zero()
    PUSH 0xe0
    SHL
    PUSH 0x80
    MSTORE
    PUSH 0x04
    PUSH 0x80
    REVERT
L5:    // JUMPDEST
    PUSH 0x0120
    MLOAD
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
    PUSH 0x02
    SLOAD
    PUSH 0x03
    SLOAD
    PUSH 0x04
    SLOAD
    PUSH 0x00
    DUP2
    EQ
    DUP1
    PUSH 0x00
    EQ
    JUMPI L8
    POP
    PUSH 0x0100
    MLOAD
    DUP1
    PUSH 0x00
    LT
    JUMPI L39
    PUSH 0x9811e0c7    // selector: ZeroShares()
    PUSH 0xe0
    SHL
    PUSH 0x80
    MSTORE
    PUSH 0x04
    PUSH 0x80
    REVERT
L39:    // JUMPDEST
    PUSH 0x0100
    MLOAD
    DUP5
    ADD
    DUP5
    DUP2
    LT
    ISZERO
    JUMPI L40
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
L40:    // JUMPDEST
    DUP1
    PUSH 0x02
    SSTORE
    PUSH 0x0120
    MLOAD
    DUP5
    ADD
    DUP5
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
    DUP1
    PUSH 0x03
    SSTORE
    DUP4
    DUP4
    ADD
    DUP4
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
    DUP1
    PUSH 0x04
    SSTORE
    DUP9
    PUSH 0x00
    MSTORE
    PUSH 0x05
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
    JUMPI L43
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
L43:    // JUMPDEST
    DUP11
    PUSH 0x00
    MSTORE
    PUSH 0x05
    PUSH 0x20
    MSTORE
    DUP1
    PUSH 0x40
    PUSH 0x00
    KECCAK256
    SSTORE
    PUSH 0x00
    PUSH 0x00
    SLOAD
    PUSH 0x23b872dd
    PUSH 0xe0
    SHL
    PUSH 0x80
    MSTORE
    DUP13
    PUSH 0x84
    MSTORE
    DUP12
    PUSH 0xa4
    MSTORE
    PUSH 0x0100
    MLOAD
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
    JUMPI L44
    PUSH 0x00
    PUSH 0x00
    REVERT
L44:    // JUMPDEST
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
    JUMPI L45
    PUSH 0x00
    PUSH 0x00
    REVERT
L45:    // JUMPDEST
    PUSH 0x01
    SWAP3
    POP
    POP
    POP
    PUSH 0x00
    DUP2
    EQ
    ISZERO
    JUMPI L46
    PUSH 0x90b8ec18    // selector: TransferFailed()
    PUSH 0xe0
    SHL
    PUSH 0x80
    MSTORE
    PUSH 0x04
    PUSH 0x80
    REVERT
L46:    // JUMPDEST
    PUSH 0x00
    PUSH 0x01
    SLOAD
    PUSH 0x23b872dd
    PUSH 0xe0
    SHL
    PUSH 0x80
    MSTORE
    DUP14
    PUSH 0x84
    MSTORE
    DUP13
    PUSH 0xa4
    MSTORE
    PUSH 0x0120
    MLOAD
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
    JUMPI L47
    PUSH 0x00
    PUSH 0x00
    REVERT
L47:    // JUMPDEST
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
    JUMPI L48
    PUSH 0x00
    PUSH 0x00
    REVERT
L48:    // JUMPDEST
    PUSH 0x01
    SWAP3
    POP
    POP
    POP
    PUSH 0x00
    DUP2
    EQ
    ISZERO
    JUMPI L49
    PUSH 0x90b8ec18    // selector: TransferFailed()
    PUSH 0xe0
    SHL
    PUSH 0x80
    MSTORE
    PUSH 0x04
    PUSH 0x80
    REVERT
L49:    // JUMPDEST
    DUP13
    PUSH 0x80
    MSTORE
    PUSH 0x0100
    MLOAD
    PUSH 0xa0
    MSTORE
    PUSH 0x0120
    MLOAD
    PUSH 0xc0
    MSTORE
    DUP8
    PUSH 0xe0
    MSTORE
    PUSH 0xbeb3885786d637a474cbc287c0a44587231633a077f0bd30354d5a4b18996fce    // topic: AddLiquidity(address,uint256,uint256,uint256)
    PUSH 0x80
    PUSH 0x80
    LOG1
    DUP8
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
    JUMP L7
L8:    // JUMPDEST
    POP
    DUP3
    PUSH 0x00
    LT
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
    DUP2
    PUSH 0x00
    LT
    JUMPI L10
    PUSH 0xf4560403    // selector: Zero()
    PUSH 0xe0
    SHL
    PUSH 0x80
    MSTORE
    PUSH 0x04
    PUSH 0x80
    REVERT
L10:    // JUMPDEST
    DUP3
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
    PUSH 0x0100
    MLOAD
    DUP2
    MUL
    PUSH 0x0100
    MLOAD
    DUP3
    DUP3
    DIV
    EQ
    DUP3
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
    DUP4
    DUP2
    DIV
    SWAP1
    POP
    DUP3
    JUMPI L13
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
L13:    // JUMPDEST
    PUSH 0x0120
    MLOAD
    DUP3
    MUL
    PUSH 0x0120
    MLOAD
    DUP4
    DUP3
    DIV
    EQ
    DUP4
    ISZERO
    OR
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
    DUP4
    DUP2
    DIV
    SWAP1
    POP
    DUP2
    DUP2
    LT
    ISZERO
    DUP1
    PUSH 0x00
    EQ
    JUMPI L16
    POP
    DUP2
    DUP1
    PUSH 0x00
    LT
    JUMPI L28
    PUSH 0x9811e0c7    // selector: ZeroShares()
    PUSH 0xe0
    SHL
    PUSH 0x80
    MSTORE
    PUSH 0x04
    PUSH 0x80
    REVERT
L28:    // JUMPDEST
    PUSH 0x0100
    MLOAD
    DUP7
    ADD
    DUP7
    DUP2
    LT
    ISZERO
    JUMPI L29
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
L29:    // JUMPDEST
    DUP1
    PUSH 0x02
    SSTORE
    PUSH 0x0120
    MLOAD
    DUP7
    ADD
    DUP7
    DUP2
    LT
    ISZERO
    JUMPI L30
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
L30:    // JUMPDEST
    DUP1
    PUSH 0x03
    SSTORE
    DUP6
    DUP4
    ADD
    DUP4
    DUP2
    LT
    ISZERO
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
    DUP1
    PUSH 0x04
    SSTORE
    DUP11
    PUSH 0x00
    MSTORE
    PUSH 0x05
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
    JUMPI L32
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
L32:    // JUMPDEST
    DUP13
    PUSH 0x00
    MSTORE
    PUSH 0x05
    PUSH 0x20
    MSTORE
    DUP1
    PUSH 0x40
    PUSH 0x00
    KECCAK256
    SSTORE
    PUSH 0x00
    PUSH 0x00
    SLOAD
    PUSH 0x23b872dd
    PUSH 0xe0
    SHL
    PUSH 0x80
    MSTORE
    DUP15
    PUSH 0x84
    MSTORE
    DUP14
    PUSH 0xa4
    MSTORE
    PUSH 0x0100
    MLOAD
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
    JUMPI L33
    PUSH 0x00
    PUSH 0x00
    REVERT
L33:    // JUMPDEST
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
    JUMPI L34
    PUSH 0x00
    PUSH 0x00
    REVERT
L34:    // JUMPDEST
    PUSH 0x01
    SWAP3
    POP
    POP
    POP
    PUSH 0x00
    DUP2
    EQ
    ISZERO
    JUMPI L35
    PUSH 0x90b8ec18    // selector: TransferFailed()
    PUSH 0xe0
    SHL
    PUSH 0x80
    MSTORE
    PUSH 0x04
    PUSH 0x80
    REVERT
L35:    // JUMPDEST
    PUSH 0x00
    PUSH 0x01
    SLOAD
    PUSH 0x23b872dd
    PUSH 0xe0
    SHL
    PUSH 0x80
    MSTORE
    DUP16
    PUSH 0x84
    MSTORE
    DUP15
    PUSH 0xa4
    MSTORE
    PUSH 0x0120
    MLOAD
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
    DUP15
    PUSH 0x80
    MSTORE
    PUSH 0x0100
    MLOAD
    PUSH 0xa0
    MSTORE
    PUSH 0x0120
    MLOAD
    PUSH 0xc0
    MSTORE
    DUP8
    PUSH 0xe0
    MSTORE
    PUSH 0xbeb3885786d637a474cbc287c0a44587231633a077f0bd30354d5a4b18996fce    // topic: AddLiquidity(address,uint256,uint256,uint256)
    PUSH 0x80
    PUSH 0x80
    LOG1
    DUP8
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
    JUMP L15
L16:    // JUMPDEST
    POP
    DUP1
    DUP1
    PUSH 0x00
    LT
    JUMPI L17
    PUSH 0x9811e0c7    // selector: ZeroShares()
    PUSH 0xe0
    SHL
    PUSH 0x80
    MSTORE
    PUSH 0x04
    PUSH 0x80
    REVERT
L17:    // JUMPDEST
    PUSH 0x0100
    MLOAD
    DUP7
    ADD
    DUP7
    DUP2
    LT
    ISZERO
    JUMPI L18
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
L18:    // JUMPDEST
    DUP1
    PUSH 0x02
    SSTORE
    PUSH 0x0120
    MLOAD
    DUP7
    ADD
    DUP7
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
    DUP1
    PUSH 0x03
    SSTORE
    DUP6
    DUP4
    ADD
    DUP4
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
    DUP1
    PUSH 0x04
    SSTORE
    DUP11
    PUSH 0x00
    MSTORE
    PUSH 0x05
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
    JUMPI L21
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
L21:    // JUMPDEST
    DUP13
    PUSH 0x00
    MSTORE
    PUSH 0x05
    PUSH 0x20
    MSTORE
    DUP1
    PUSH 0x40
    PUSH 0x00
    KECCAK256
    SSTORE
    PUSH 0x00
    PUSH 0x00
    SLOAD
    PUSH 0x23b872dd
    PUSH 0xe0
    SHL
    PUSH 0x80
    MSTORE
    DUP15
    PUSH 0x84
    MSTORE
    DUP14
    PUSH 0xa4
    MSTORE
    PUSH 0x0100
    MLOAD
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
    JUMPI L22
    PUSH 0x00
    PUSH 0x00
    REVERT
L22:    // JUMPDEST
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
    JUMPI L23
    PUSH 0x00
    PUSH 0x00
    REVERT
L23:    // JUMPDEST
    PUSH 0x01
    SWAP3
    POP
    POP
    POP
    PUSH 0x00
    DUP2
    EQ
    ISZERO
    JUMPI L24
    PUSH 0x90b8ec18    // selector: TransferFailed()
    PUSH 0xe0
    SHL
    PUSH 0x80
    MSTORE
    PUSH 0x04
    PUSH 0x80
    REVERT
L24:    // JUMPDEST
    PUSH 0x00
    PUSH 0x01
    SLOAD
    PUSH 0x23b872dd
    PUSH 0xe0
    SHL
    PUSH 0x80
    MSTORE
    DUP16
    PUSH 0x84
    MSTORE
    DUP15
    PUSH 0xa4
    MSTORE
    PUSH 0x0120
    MLOAD
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
    JUMPI L25
    PUSH 0x00
    PUSH 0x00
    REVERT
L25:    // JUMPDEST
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
    JUMPI L26
    PUSH 0x00
    PUSH 0x00
    REVERT
L26:    // JUMPDEST
    PUSH 0x01
    SWAP3
    POP
    POP
    POP
    PUSH 0x00
    DUP2
    EQ
    ISZERO
    JUMPI L27
    PUSH 0x90b8ec18    // selector: TransferFailed()
    PUSH 0xe0
    SHL
    PUSH 0x80
    MSTORE
    PUSH 0x04
    PUSH 0x80
    REVERT
L27:    // JUMPDEST
    DUP15
    PUSH 0x80
    MSTORE
    PUSH 0x0100
    MLOAD
    PUSH 0xa0
    MSTORE
    PUSH 0x0120
    MLOAD
    PUSH 0xc0
    MSTORE
    DUP8
    PUSH 0xe0
    MSTORE
    PUSH 0xbeb3885786d637a474cbc287c0a44587231633a077f0bd30354d5a4b18996fce    // topic: AddLiquidity(address,uint256,uint256,uint256)
    PUSH 0x80
    PUSH 0x80
    LOG1
    DUP8
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
L15:    // JUMPDEST
    POP
    POP
L7:    // JUMPDEST
    POP
    POP
    POP
    POP
    POP
    JUMP L2
L50:    // JUMPDEST
    POP
    PUSH 0x24
    CALLDATASIZE
    LT
    ISZERO
    JUMPI L51
    PUSH 0x00
    PUSH 0x00
    REVERT
L51:    // JUMPDEST
    PUSH 0x04
    CALLDATALOAD
    DUP1
    PUSH 0x00
    LT
    JUMPI L52
    PUSH 0xf4560403    // selector: Zero()
    PUSH 0xe0
    SHL
    PUSH 0x80
    MSTORE
    PUSH 0x04
    PUSH 0x80
    REVERT
L52:    // JUMPDEST
    CALLER
    DUP1
    PUSH 0x00
    MSTORE
    PUSH 0x05
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
    JUMPI L53
    PUSH 0x39996567    // selector: InsufficientShares()
    PUSH 0xe0
    SHL
    PUSH 0x80
    MSTORE
    PUSH 0x04
    PUSH 0x80
    REVERT
L53:    // JUMPDEST
    PUSH 0x02
    SLOAD
    PUSH 0x03
    SLOAD
    PUSH 0x04
    SLOAD
    DUP1
    PUSH 0x00
    LT
    JUMPI L54
    PUSH 0xf4560403    // selector: Zero()
    PUSH 0xe0
    SHL
    PUSH 0x80
    MSTORE
    PUSH 0x04
    PUSH 0x80
    REVERT
L54:    // JUMPDEST
    DUP1
    JUMPI L55
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
L55:    // JUMPDEST
    DUP6
    DUP4
    MUL
    DUP7
    DUP5
    DUP3
    DIV
    EQ
    DUP5
    ISZERO
    OR
    JUMPI L56
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
L56:    // JUMPDEST
    DUP2
    DUP2
    DIV
    SWAP1
    POP
    DUP2
    JUMPI L57
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
L57:    // JUMPDEST
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
    JUMPI L58
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
L58:    // JUMPDEST
    DUP3
    DUP2
    DIV
    SWAP1
    POP
    DUP2
    PUSH 0x00
    LT
    JUMPI L59
    PUSH 0x1078b533    // selector: ZeroOut()
    PUSH 0xe0
    SHL
    PUSH 0x80
    MSTORE
    PUSH 0x04
    PUSH 0x80
    REVERT
L59:    // JUMPDEST
    DUP1
    PUSH 0x00
    LT
    JUMPI L60
    PUSH 0x1078b533    // selector: ZeroOut()
    PUSH 0xe0
    SHL
    PUSH 0x80
    MSTORE
    PUSH 0x04
    PUSH 0x80
    REVERT
L60:    // JUMPDEST
    DUP8
    DUP7
    LT
    ISZERO
    JUMPI L61
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
L61:    // JUMPDEST
    DUP8
    DUP7
    SUB
    DUP8
    PUSH 0x00
    MSTORE
    PUSH 0x05
    PUSH 0x20
    MSTORE
    DUP1
    PUSH 0x40
    PUSH 0x00
    KECCAK256
    SSTORE
    DUP9
    DUP5
    LT
    ISZERO
    JUMPI L62
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
L62:    // JUMPDEST
    DUP9
    DUP5
    SUB
    DUP1
    PUSH 0x04
    SSTORE
    DUP4
    DUP8
    LT
    ISZERO
    JUMPI L63
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
L63:    // JUMPDEST
    DUP4
    DUP8
    SUB
    DUP1
    PUSH 0x02
    SSTORE
    DUP4
    DUP8
    LT
    ISZERO
    JUMPI L64
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
L64:    // JUMPDEST
    DUP4
    DUP8
    SUB
    DUP1
    PUSH 0x03
    SSTORE
    PUSH 0x00
    PUSH 0x00
    SLOAD
    PUSH 0xa9059cbb
    PUSH 0xe0
    SHL
    PUSH 0x80
    MSTORE
    DUP13
    PUSH 0x84
    MSTORE
    DUP8
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
    JUMPI L65
    PUSH 0x00
    PUSH 0x00
    REVERT
L65:    // JUMPDEST
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
    JUMPI L66
    PUSH 0x00
    PUSH 0x00
    REVERT
L66:    // JUMPDEST
    PUSH 0x01
    SWAP3
    POP
    POP
    POP
    PUSH 0x00
    DUP2
    EQ
    ISZERO
    JUMPI L67
    PUSH 0x90b8ec18    // selector: TransferFailed()
    PUSH 0xe0
    SHL
    PUSH 0x80
    MSTORE
    PUSH 0x04
    PUSH 0x80
    REVERT
L67:    // JUMPDEST
    PUSH 0x00
    PUSH 0x01
    SLOAD
    PUSH 0xa9059cbb
    PUSH 0xe0
    SHL
    PUSH 0x80
    MSTORE
    DUP14
    PUSH 0x84
    MSTORE
    DUP8
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
    JUMPI L68
    PUSH 0x00
    PUSH 0x00
    REVERT
L68:    // JUMPDEST
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
    JUMPI L69
    PUSH 0x00
    PUSH 0x00
    REVERT
L69:    // JUMPDEST
    PUSH 0x01
    SWAP3
    POP
    POP
    POP
    PUSH 0x00
    DUP2
    EQ
    ISZERO
    JUMPI L70
    PUSH 0x90b8ec18    // selector: TransferFailed()
    PUSH 0xe0
    SHL
    PUSH 0x80
    MSTORE
    PUSH 0x04
    PUSH 0x80
    REVERT
L70:    // JUMPDEST
    DUP13
    PUSH 0x80
    MSTORE
    DUP8
    PUSH 0xa0
    MSTORE
    DUP7
    PUSH 0xc0
    MSTORE
    DUP14
    PUSH 0xe0
    MSTORE
    PUSH 0x59c3a0b60c6ab7deb62e1440c9e72441db6db7dfe514dba8cb18e60c0d896efa    // topic: RemoveLiquidity(address,uint256,uint256,uint256)
    PUSH 0x80
    PUSH 0x80
    LOG1
    DUP8
    PUSH 0x80
    MSTORE
    DUP7
    PUSH 0xa0
    MSTORE
    PUSH 0x40
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
    POP
    POP
    JUMP L2
L71:    // JUMPDEST
    POP
    PUSH 0x44
    CALLDATASIZE
    LT
    ISZERO
    JUMPI L72
    PUSH 0x00
    PUSH 0x00
    REVERT
L72:    // JUMPDEST
    PUSH 0x04
    CALLDATALOAD
    PUSH 0x0100
    MSTORE
    PUSH 0x24
    CALLDATALOAD
    PUSH 0x0100
    MLOAD
    PUSH 0x00
    LT
    JUMPI L73
    PUSH 0xf4560403    // selector: Zero()
    PUSH 0xe0
    SHL
    PUSH 0x80
    MSTORE
    PUSH 0x04
    PUSH 0x80
    REVERT
L73:    // JUMPDEST
    PUSH 0x02
    SLOAD
    PUSH 0x03
    SLOAD
    DUP2
    PUSH 0x00
    LT
    JUMPI L74
    PUSH 0xf4560403    // selector: Zero()
    PUSH 0xe0
    SHL
    PUSH 0x80
    MSTORE
    PUSH 0x04
    PUSH 0x80
    REVERT
L74:    // JUMPDEST
    DUP1
    PUSH 0x00
    LT
    JUMPI L75
    PUSH 0xf4560403    // selector: Zero()
    PUSH 0xe0
    SHL
    PUSH 0x80
    MSTORE
    PUSH 0x04
    PUSH 0x80
    REVERT
L75:    // JUMPDEST
    PUSH 0x2710
    JUMPI L76
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
L76:    // JUMPDEST
    PUSH 0x26f2
    PUSH 0x0100
    MLOAD
    MUL
    PUSH 0x26f2
    PUSH 0x0100
    MLOAD
    DUP3
    DIV
    EQ
    PUSH 0x0100
    MLOAD
    ISZERO
    OR
    JUMPI L77
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
L77:    // JUMPDEST
    PUSH 0x2710
    DUP2
    DIV
    SWAP1
    POP
    DUP1
    DUP4
    ADD
    DUP4
    DUP2
    LT
    ISZERO
    JUMPI L78
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
L78:    // JUMPDEST
    DUP1
    JUMPI L79
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
L79:    // JUMPDEST
    DUP2
    DUP4
    MUL
    PUSH 0x0120
    MSTORE
    DUP2
    DUP4
    PUSH 0x0120
    MLOAD
    DIV
    EQ
    DUP4
    ISZERO
    OR
    JUMPI L80
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
L80:    // JUMPDEST
    DUP1
    PUSH 0x0120
    MLOAD
    DIV
    PUSH 0x0120
    MSTORE
    DUP5
    PUSH 0x0120
    MLOAD
    LT
    ISZERO
    JUMPI L81
    PUSH 0xbb2875c3    // selector: InsufficientOutput()
    PUSH 0xe0
    SHL
    PUSH 0x80
    MSTORE
    PUSH 0x04
    PUSH 0x80
    REVERT
L81:    // JUMPDEST
    PUSH 0x0120
    MLOAD
    PUSH 0x00
    LT
    JUMPI L82
    PUSH 0x1078b533    // selector: ZeroOut()
    PUSH 0xe0
    SHL
    PUSH 0x80
    MSTORE
    PUSH 0x04
    PUSH 0x80
    REVERT
L82:    // JUMPDEST
    PUSH 0x07
    SLOAD
    PUSH 0x08
    SLOAD
    PUSH 0x00
    DUP3
    EQ
    DUP1
    PUSH 0x00
    EQ
    JUMPI L84
    POP
    PUSH 0x00
    PUSH 0x2710
    JUMPI L100
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
L100:    // JUMPDEST
    PUSH 0x26f2
    PUSH 0x0100
    MLOAD
    MUL
    PUSH 0x26f2
    PUSH 0x0100
    MLOAD
    DUP3
    DIV
    EQ
    PUSH 0x0100
    MLOAD
    ISZERO
    OR
    JUMPI L101
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
L101:    // JUMPDEST
    PUSH 0x2710
    DUP2
    DIV
    SWAP1
    POP
    DUP1
    PUSH 0x0100
    MLOAD
    LT
    ISZERO
    JUMPI L102
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
L102:    // JUMPDEST
    DUP1
    PUSH 0x0100
    MLOAD
    SUB
    PUSH 0x2710
    JUMPI L103
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
L103:    // JUMPDEST
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
    JUMPI L104
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
L104:    // JUMPDEST
    PUSH 0x2710
    DUP2
    DIV
    SWAP1
    POP
    DUP1
    PUSH 0x0100
    MLOAD
    LT
    ISZERO
    JUMPI L105
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
L105:    // JUMPDEST
    DUP1
    PUSH 0x0100
    MLOAD
    SUB
    DUP1
    DUP12
    ADD
    DUP12
    DUP2
    LT
    ISZERO
    JUMPI L106
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
L106:    // JUMPDEST
    DUP1
    PUSH 0x02
    SSTORE
    PUSH 0x0120
    MLOAD
    DUP12
    LT
    ISZERO
    JUMPI L107
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
L107:    // JUMPDEST
    PUSH 0x0120
    MLOAD
    DUP12
    SUB
    DUP1
    PUSH 0x03
    SSTORE
    PUSH 0x09
    SLOAD
    DUP5
    DUP2
    ADD
    DUP2
    DUP2
    LT
    ISZERO
    JUMPI L108
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
L108:    // JUMPDEST
    DUP1
    PUSH 0x09
    SSTORE
    CALLER
    ADDRESS
    PUSH 0x00
    PUSH 0x00
    SLOAD
    PUSH 0x23b872dd
    PUSH 0xe0
    SHL
    PUSH 0x80
    MSTORE
    DUP4
    PUSH 0x84
    MSTORE
    DUP3
    PUSH 0xa4
    MSTORE
    PUSH 0x0100
    MLOAD
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
    JUMPI L109
    PUSH 0x00
    PUSH 0x00
    REVERT
L109:    // JUMPDEST
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
    JUMPI L110
    PUSH 0x00
    PUSH 0x00
    REVERT
L110:    // JUMPDEST
    PUSH 0x01
    SWAP3
    POP
    POP
    POP
    PUSH 0x00
    DUP2
    EQ
    ISZERO
    JUMPI L111
    PUSH 0x90b8ec18    // selector: TransferFailed()
    PUSH 0xe0
    SHL
    PUSH 0x80
    MSTORE
    PUSH 0x04
    PUSH 0x80
    REVERT
L111:    // JUMPDEST
    PUSH 0x00
    PUSH 0x01
    SLOAD
    PUSH 0xa9059cbb
    PUSH 0xe0
    SHL
    PUSH 0x80
    MSTORE
    DUP5
    PUSH 0x84
    MSTORE
    PUSH 0x0120
    MLOAD
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
    JUMPI L112
    PUSH 0x00
    PUSH 0x00
    REVERT
L112:    // JUMPDEST
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
    JUMPI L113
    PUSH 0x00
    PUSH 0x00
    REVERT
L113:    // JUMPDEST
    PUSH 0x01
    SWAP3
    POP
    POP
    POP
    PUSH 0x00
    DUP2
    EQ
    ISZERO
    JUMPI L114
    PUSH 0x90b8ec18    // selector: TransferFailed()
    PUSH 0xe0
    SHL
    PUSH 0x80
    MSTORE
    PUSH 0x04
    PUSH 0x80
    REVERT
L114:    // JUMPDEST
    DUP4
    PUSH 0x80
    MSTORE
    PUSH 0x0100
    MLOAD
    PUSH 0xa0
    MSTORE
    PUSH 0x0120
    MLOAD
    PUSH 0xc0
    MSTORE
    PUSH 0x268d208c45ec3d7213f545c4402b1bc7f11b332757a4e0d84ff4d37b90db1fca    // topic: Swap0for1(address,uint256,uint256)
    PUSH 0x60
    PUSH 0x80
    LOG1
    PUSH 0x0120
    MLOAD
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
    POP
    JUMP L83
L84:    // JUMPDEST
    POP
    DUP1
    PUSH 0x2710
    JUMPI L85
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
L85:    // JUMPDEST
    PUSH 0x26f2
    PUSH 0x0100
    MLOAD
    MUL
    PUSH 0x26f2
    PUSH 0x0100
    MLOAD
    DUP3
    DIV
    EQ
    PUSH 0x0100
    MLOAD
    ISZERO
    OR
    JUMPI L86
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
L86:    // JUMPDEST
    PUSH 0x2710
    DUP2
    DIV
    SWAP1
    POP
    DUP1
    PUSH 0x0100
    MLOAD
    LT
    ISZERO
    JUMPI L87
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
L87:    // JUMPDEST
    DUP1
    PUSH 0x0100
    MLOAD
    SUB
    PUSH 0x2710
    JUMPI L88
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
L88:    // JUMPDEST
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
    JUMPI L89
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
L89:    // JUMPDEST
    PUSH 0x2710
    DUP2
    DIV
    SWAP1
    POP
    DUP1
    PUSH 0x0100
    MLOAD
    LT
    ISZERO
    JUMPI L90
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
L90:    // JUMPDEST
    DUP1
    PUSH 0x0100
    MLOAD
    SUB
    DUP1
    DUP12
    ADD
    DUP12
    DUP2
    LT
    ISZERO
    JUMPI L91
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
L91:    // JUMPDEST
    DUP1
    PUSH 0x02
    SSTORE
    PUSH 0x0120
    MLOAD
    DUP12
    LT
    ISZERO
    JUMPI L92
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
L92:    // JUMPDEST
    PUSH 0x0120
    MLOAD
    DUP12
    SUB
    DUP1
    PUSH 0x03
    SSTORE
    PUSH 0x09
    SLOAD
    DUP5
    DUP2
    ADD
    DUP2
    DUP2
    LT
    ISZERO
    JUMPI L93
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
L93:    // JUMPDEST
    DUP1
    PUSH 0x09
    SSTORE
    CALLER
    ADDRESS
    PUSH 0x00
    PUSH 0x00
    SLOAD
    PUSH 0x23b872dd
    PUSH 0xe0
    SHL
    PUSH 0x80
    MSTORE
    DUP4
    PUSH 0x84
    MSTORE
    DUP3
    PUSH 0xa4
    MSTORE
    PUSH 0x0100
    MLOAD
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
    JUMPI L94
    PUSH 0x00
    PUSH 0x00
    REVERT
L94:    // JUMPDEST
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
    JUMPI L95
    PUSH 0x00
    PUSH 0x00
    REVERT
L95:    // JUMPDEST
    PUSH 0x01
    SWAP3
    POP
    POP
    POP
    PUSH 0x00
    DUP2
    EQ
    ISZERO
    JUMPI L96
    PUSH 0x90b8ec18    // selector: TransferFailed()
    PUSH 0xe0
    SHL
    PUSH 0x80
    MSTORE
    PUSH 0x04
    PUSH 0x80
    REVERT
L96:    // JUMPDEST
    PUSH 0x00
    PUSH 0x01
    SLOAD
    PUSH 0xa9059cbb
    PUSH 0xe0
    SHL
    PUSH 0x80
    MSTORE
    DUP5
    PUSH 0x84
    MSTORE
    PUSH 0x0120
    MLOAD
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
    JUMPI L97
    PUSH 0x00
    PUSH 0x00
    REVERT
L97:    // JUMPDEST
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
    JUMPI L98
    PUSH 0x00
    PUSH 0x00
    REVERT
L98:    // JUMPDEST
    PUSH 0x01
    SWAP3
    POP
    POP
    POP
    PUSH 0x00
    DUP2
    EQ
    ISZERO
    JUMPI L99
    PUSH 0x90b8ec18    // selector: TransferFailed()
    PUSH 0xe0
    SHL
    PUSH 0x80
    MSTORE
    PUSH 0x04
    PUSH 0x80
    REVERT
L99:    // JUMPDEST
    DUP4
    PUSH 0x80
    MSTORE
    PUSH 0x0100
    MLOAD
    PUSH 0xa0
    MSTORE
    PUSH 0x0120
    MLOAD
    PUSH 0xc0
    MSTORE
    PUSH 0x268d208c45ec3d7213f545c4402b1bc7f11b332757a4e0d84ff4d37b90db1fca    // topic: Swap0for1(address,uint256,uint256)
    PUSH 0x60
    PUSH 0x80
    LOG1
    PUSH 0x0120
    MLOAD
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
    POP
L83:    // JUMPDEST
    POP
    POP
    POP
    POP
    POP
    POP
    POP
    JUMP L2
L115:    // JUMPDEST
    POP
    PUSH 0x44
    CALLDATASIZE
    LT
    ISZERO
    JUMPI L116
    PUSH 0x00
    PUSH 0x00
    REVERT
L116:    // JUMPDEST
    PUSH 0x04
    CALLDATALOAD
    PUSH 0x0100
    MSTORE
    PUSH 0x24
    CALLDATALOAD
    PUSH 0x0100
    MLOAD
    PUSH 0x00
    LT
    JUMPI L117
    PUSH 0xf4560403    // selector: Zero()
    PUSH 0xe0
    SHL
    PUSH 0x80
    MSTORE
    PUSH 0x04
    PUSH 0x80
    REVERT
L117:    // JUMPDEST
    PUSH 0x02
    SLOAD
    PUSH 0x03
    SLOAD
    DUP2
    PUSH 0x00
    LT
    JUMPI L118
    PUSH 0xf4560403    // selector: Zero()
    PUSH 0xe0
    SHL
    PUSH 0x80
    MSTORE
    PUSH 0x04
    PUSH 0x80
    REVERT
L118:    // JUMPDEST
    DUP1
    PUSH 0x00
    LT
    JUMPI L119
    PUSH 0xf4560403    // selector: Zero()
    PUSH 0xe0
    SHL
    PUSH 0x80
    MSTORE
    PUSH 0x04
    PUSH 0x80
    REVERT
L119:    // JUMPDEST
    PUSH 0x2710
    JUMPI L120
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
L120:    // JUMPDEST
    PUSH 0x26f2
    PUSH 0x0100
    MLOAD
    MUL
    PUSH 0x26f2
    PUSH 0x0100
    MLOAD
    DUP3
    DIV
    EQ
    PUSH 0x0100
    MLOAD
    ISZERO
    OR
    JUMPI L121
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
L121:    // JUMPDEST
    PUSH 0x2710
    DUP2
    DIV
    SWAP1
    POP
    DUP1
    DUP3
    ADD
    DUP3
    DUP2
    LT
    ISZERO
    JUMPI L122
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
L122:    // JUMPDEST
    DUP1
    JUMPI L123
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
L123:    // JUMPDEST
    DUP2
    DUP5
    MUL
    PUSH 0x0120
    MSTORE
    DUP2
    DUP5
    PUSH 0x0120
    MLOAD
    DIV
    EQ
    DUP5
    ISZERO
    OR
    JUMPI L124
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
L124:    // JUMPDEST
    DUP1
    PUSH 0x0120
    MLOAD
    DIV
    PUSH 0x0120
    MSTORE
    DUP5
    PUSH 0x0120
    MLOAD
    LT
    ISZERO
    JUMPI L125
    PUSH 0xbb2875c3    // selector: InsufficientOutput()
    PUSH 0xe0
    SHL
    PUSH 0x80
    MSTORE
    PUSH 0x04
    PUSH 0x80
    REVERT
L125:    // JUMPDEST
    PUSH 0x0120
    MLOAD
    PUSH 0x00
    LT
    JUMPI L126
    PUSH 0x1078b533    // selector: ZeroOut()
    PUSH 0xe0
    SHL
    PUSH 0x80
    MSTORE
    PUSH 0x04
    PUSH 0x80
    REVERT
L126:    // JUMPDEST
    PUSH 0x07
    SLOAD
    PUSH 0x08
    SLOAD
    PUSH 0x00
    DUP3
    EQ
    DUP1
    PUSH 0x00
    EQ
    JUMPI L128
    POP
    PUSH 0x00
    PUSH 0x2710
    JUMPI L144
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
L144:    // JUMPDEST
    PUSH 0x26f2
    PUSH 0x0100
    MLOAD
    MUL
    PUSH 0x26f2
    PUSH 0x0100
    MLOAD
    DUP3
    DIV
    EQ
    PUSH 0x0100
    MLOAD
    ISZERO
    OR
    JUMPI L145
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
L145:    // JUMPDEST
    PUSH 0x2710
    DUP2
    DIV
    SWAP1
    POP
    DUP1
    PUSH 0x0100
    MLOAD
    LT
    ISZERO
    JUMPI L146
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
L146:    // JUMPDEST
    DUP1
    PUSH 0x0100
    MLOAD
    SUB
    PUSH 0x2710
    JUMPI L147
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
L147:    // JUMPDEST
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
    JUMPI L148
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
L148:    // JUMPDEST
    PUSH 0x2710
    DUP2
    DIV
    SWAP1
    POP
    DUP1
    PUSH 0x0100
    MLOAD
    LT
    ISZERO
    JUMPI L149
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
L149:    // JUMPDEST
    DUP1
    PUSH 0x0100
    MLOAD
    SUB
    DUP1
    DUP11
    ADD
    DUP11
    DUP2
    LT
    ISZERO
    JUMPI L150
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
L150:    // JUMPDEST
    DUP1
    PUSH 0x03
    SSTORE
    PUSH 0x0120
    MLOAD
    DUP13
    LT
    ISZERO
    JUMPI L151
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
L151:    // JUMPDEST
    PUSH 0x0120
    MLOAD
    DUP13
    SUB
    DUP1
    PUSH 0x02
    SSTORE
    PUSH 0x0a
    SLOAD
    DUP5
    DUP2
    ADD
    DUP2
    DUP2
    LT
    ISZERO
    JUMPI L152
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
L152:    // JUMPDEST
    DUP1
    PUSH 0x0a
    SSTORE
    CALLER
    ADDRESS
    PUSH 0x00
    PUSH 0x01
    SLOAD
    PUSH 0x23b872dd
    PUSH 0xe0
    SHL
    PUSH 0x80
    MSTORE
    DUP4
    PUSH 0x84
    MSTORE
    DUP3
    PUSH 0xa4
    MSTORE
    PUSH 0x0100
    MLOAD
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
    JUMPI L153
    PUSH 0x00
    PUSH 0x00
    REVERT
L153:    // JUMPDEST
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
    JUMPI L154
    PUSH 0x00
    PUSH 0x00
    REVERT
L154:    // JUMPDEST
    PUSH 0x01
    SWAP3
    POP
    POP
    POP
    PUSH 0x00
    DUP2
    EQ
    ISZERO
    JUMPI L155
    PUSH 0x90b8ec18    // selector: TransferFailed()
    PUSH 0xe0
    SHL
    PUSH 0x80
    MSTORE
    PUSH 0x04
    PUSH 0x80
    REVERT
L155:    // JUMPDEST
    PUSH 0x00
    PUSH 0x00
    SLOAD
    PUSH 0xa9059cbb
    PUSH 0xe0
    SHL
    PUSH 0x80
    MSTORE
    DUP5
    PUSH 0x84
    MSTORE
    PUSH 0x0120
    MLOAD
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
    JUMPI L156
    PUSH 0x00
    PUSH 0x00
    REVERT
L156:    // JUMPDEST
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
    JUMPI L157
    PUSH 0x00
    PUSH 0x00
    REVERT
L157:    // JUMPDEST
    PUSH 0x01
    SWAP3
    POP
    POP
    POP
    PUSH 0x00
    DUP2
    EQ
    ISZERO
    JUMPI L158
    PUSH 0x90b8ec18    // selector: TransferFailed()
    PUSH 0xe0
    SHL
    PUSH 0x80
    MSTORE
    PUSH 0x04
    PUSH 0x80
    REVERT
L158:    // JUMPDEST
    DUP4
    PUSH 0x80
    MSTORE
    PUSH 0x0100
    MLOAD
    PUSH 0xa0
    MSTORE
    PUSH 0x0120
    MLOAD
    PUSH 0xc0
    MSTORE
    PUSH 0xec43a82fae8c251f7aae4f79accf59c765bd798d597ccfd95beef20bf096cc9e    // topic: Swap1for0(address,uint256,uint256)
    PUSH 0x60
    PUSH 0x80
    LOG1
    PUSH 0x0120
    MLOAD
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
    POP
    JUMP L127
L128:    // JUMPDEST
    POP
    DUP1
    PUSH 0x2710
    JUMPI L129
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
L129:    // JUMPDEST
    PUSH 0x26f2
    PUSH 0x0100
    MLOAD
    MUL
    PUSH 0x26f2
    PUSH 0x0100
    MLOAD
    DUP3
    DIV
    EQ
    PUSH 0x0100
    MLOAD
    ISZERO
    OR
    JUMPI L130
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
L130:    // JUMPDEST
    PUSH 0x2710
    DUP2
    DIV
    SWAP1
    POP
    DUP1
    PUSH 0x0100
    MLOAD
    LT
    ISZERO
    JUMPI L131
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
L131:    // JUMPDEST
    DUP1
    PUSH 0x0100
    MLOAD
    SUB
    PUSH 0x2710
    JUMPI L132
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
L132:    // JUMPDEST
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
    JUMPI L133
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
L133:    // JUMPDEST
    PUSH 0x2710
    DUP2
    DIV
    SWAP1
    POP
    DUP1
    PUSH 0x0100
    MLOAD
    LT
    ISZERO
    JUMPI L134
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
L134:    // JUMPDEST
    DUP1
    PUSH 0x0100
    MLOAD
    SUB
    DUP1
    DUP11
    ADD
    DUP11
    DUP2
    LT
    ISZERO
    JUMPI L135
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
L135:    // JUMPDEST
    DUP1
    PUSH 0x03
    SSTORE
    PUSH 0x0120
    MLOAD
    DUP13
    LT
    ISZERO
    JUMPI L136
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
L136:    // JUMPDEST
    PUSH 0x0120
    MLOAD
    DUP13
    SUB
    DUP1
    PUSH 0x02
    SSTORE
    PUSH 0x0a
    SLOAD
    DUP5
    DUP2
    ADD
    DUP2
    DUP2
    LT
    ISZERO
    JUMPI L137
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
L137:    // JUMPDEST
    DUP1
    PUSH 0x0a
    SSTORE
    CALLER
    ADDRESS
    PUSH 0x00
    PUSH 0x01
    SLOAD
    PUSH 0x23b872dd
    PUSH 0xe0
    SHL
    PUSH 0x80
    MSTORE
    DUP4
    PUSH 0x84
    MSTORE
    DUP3
    PUSH 0xa4
    MSTORE
    PUSH 0x0100
    MLOAD
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
    JUMPI L138
    PUSH 0x00
    PUSH 0x00
    REVERT
L138:    // JUMPDEST
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
    JUMPI L139
    PUSH 0x00
    PUSH 0x00
    REVERT
L139:    // JUMPDEST
    PUSH 0x01
    SWAP3
    POP
    POP
    POP
    PUSH 0x00
    DUP2
    EQ
    ISZERO
    JUMPI L140
    PUSH 0x90b8ec18    // selector: TransferFailed()
    PUSH 0xe0
    SHL
    PUSH 0x80
    MSTORE
    PUSH 0x04
    PUSH 0x80
    REVERT
L140:    // JUMPDEST
    PUSH 0x00
    PUSH 0x00
    SLOAD
    PUSH 0xa9059cbb
    PUSH 0xe0
    SHL
    PUSH 0x80
    MSTORE
    DUP5
    PUSH 0x84
    MSTORE
    PUSH 0x0120
    MLOAD
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
    JUMPI L141
    PUSH 0x00
    PUSH 0x00
    REVERT
L141:    // JUMPDEST
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
    JUMPI L142
    PUSH 0x00
    PUSH 0x00
    REVERT
L142:    // JUMPDEST
    PUSH 0x01
    SWAP3
    POP
    POP
    POP
    PUSH 0x00
    DUP2
    EQ
    ISZERO
    JUMPI L143
    PUSH 0x90b8ec18    // selector: TransferFailed()
    PUSH 0xe0
    SHL
    PUSH 0x80
    MSTORE
    PUSH 0x04
    PUSH 0x80
    REVERT
L143:    // JUMPDEST
    DUP4
    PUSH 0x80
    MSTORE
    PUSH 0x0100
    MLOAD
    PUSH 0xa0
    MSTORE
    PUSH 0x0120
    MLOAD
    PUSH 0xc0
    MSTORE
    PUSH 0xec43a82fae8c251f7aae4f79accf59c765bd798d597ccfd95beef20bf096cc9e    // topic: Swap1for0(address,uint256,uint256)
    PUSH 0x60
    PUSH 0x80
    LOG1
    PUSH 0x0120
    MLOAD
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
    POP
L127:    // JUMPDEST
    POP
    POP
    POP
    POP
    POP
    POP
    POP
    JUMP L2
L159:    // JUMPDEST
    POP
    PUSH 0x24
    CALLDATASIZE
    LT
    ISZERO
    JUMPI L160
    PUSH 0x00
    PUSH 0x00
    REVERT
L160:    // JUMPDEST
    PUSH 0x04
    CALLDATALOAD
    CALLER
    PUSH 0x06
    SLOAD
    DUP1
    DUP3
    EQ
    JUMPI L161
    PUSH 0x30cd7471    // selector: NotOwner()
    PUSH 0xe0
    SHL
    PUSH 0x80
    MSTORE
    PUSH 0x04
    PUSH 0x80
    REVERT
L161:    // JUMPDEST
    DUP3
    PUSH 0x2710
    LT
    ISZERO
    JUMPI L162
    PUSH 0xcd4e6167    // selector: FeeTooHigh()
    PUSH 0xe0
    SHL
    PUSH 0x80
    MSTORE
    PUSH 0x04
    PUSH 0x80
    REVERT
L162:    // JUMPDEST
    DUP3
    PUSH 0x08
    SSTORE
    DUP3
    PUSH 0x80
    MSTORE
    PUSH 0xac9f8df6116458aab7d2642e648145d5f693b4d6a1f0dff57db25547224c8b55    // topic: ProtocolShareSet(uint256)
    PUSH 0x20
    PUSH 0x80
    LOG1
    STOP
    POP
    POP
    POP
    JUMP L2
L163:    // JUMPDEST
    POP
    PUSH 0x24
    CALLDATASIZE
    LT
    ISZERO
    JUMPI L164
    PUSH 0x00
    PUSH 0x00
    REVERT
L164:    // JUMPDEST
    PUSH 0x04
    CALLDATALOAD
    CALLER
    PUSH 0x06
    SLOAD
    DUP1
    DUP3
    EQ
    JUMPI L165
    PUSH 0x30cd7471    // selector: NotOwner()
    PUSH 0xe0
    SHL
    PUSH 0x80
    MSTORE
    PUSH 0x04
    PUSH 0x80
    REVERT
L165:    // JUMPDEST
    DUP3
    PUSH 0x07
    SSTORE
    DUP3
    PUSH 0x80
    MSTORE
    PUSH 0xe7ba424f407983edfb652af33e51f926d1d41a22bb4850c65eb21c02e378957c    // topic: FeeToSet(address)
    PUSH 0x20
    PUSH 0x80
    LOG1
    STOP
    POP
    POP
    POP
    JUMP L2
L166:    // JUMPDEST
    POP
    PUSH 0x04
    CALLDATASIZE
    LT
    ISZERO
    JUMPI L167
    PUSH 0x00
    PUSH 0x00
    REVERT
L167:    // JUMPDEST
    CALLER
    PUSH 0x07
    SLOAD
    PUSH 0x00
    DUP2
    EQ
    ISZERO
    JUMPI L168
    PUSH 0x6f74ca5d    // selector: NoFeeTo()
    PUSH 0xe0
    SHL
    PUSH 0x80
    MSTORE
    PUSH 0x04
    PUSH 0x80
    REVERT
L168:    // JUMPDEST
    DUP1
    DUP3
    EQ
    JUMPI L169
    PUSH 0x30cd7471    // selector: NotOwner()
    PUSH 0xe0
    SHL
    PUSH 0x80
    MSTORE
    PUSH 0x04
    PUSH 0x80
    REVERT
L169:    // JUMPDEST
    PUSH 0x09
    SLOAD
    PUSH 0x0a
    SLOAD
    PUSH 0x00
    PUSH 0x09
    SSTORE
    PUSH 0x00
    PUSH 0x0a
    SSTORE
    PUSH 0x00
    PUSH 0x00
    SLOAD
    PUSH 0xa9059cbb
    PUSH 0xe0
    SHL
    PUSH 0x80
    MSTORE
    DUP6
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
    DUP6
    PUSH 0x0f4240
    CALL
    DUP1
    JUMPI L170
    PUSH 0x00
    PUSH 0x00
    REVERT
L170:    // JUMPDEST
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
    JUMPI L171
    PUSH 0x00
    PUSH 0x00
    REVERT
L171:    // JUMPDEST
    PUSH 0x01
    SWAP3
    POP
    POP
    POP
    PUSH 0x00
    DUP2
    EQ
    ISZERO
    JUMPI L172
    PUSH 0x90b8ec18    // selector: TransferFailed()
    PUSH 0xe0
    SHL
    PUSH 0x80
    MSTORE
    PUSH 0x04
    PUSH 0x80
    REVERT
L172:    // JUMPDEST
    PUSH 0x00
    PUSH 0x01
    SLOAD
    PUSH 0xa9059cbb
    PUSH 0xe0
    SHL
    PUSH 0x80
    MSTORE
    DUP7
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
    DUP6
    PUSH 0x0f4240
    CALL
    DUP1
    JUMPI L173
    PUSH 0x00
    PUSH 0x00
    REVERT
L173:    // JUMPDEST
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
    JUMPI L174
    PUSH 0x00
    PUSH 0x00
    REVERT
L174:    // JUMPDEST
    PUSH 0x01
    SWAP3
    POP
    POP
    POP
    PUSH 0x00
    DUP2
    EQ
    ISZERO
    JUMPI L175
    PUSH 0x90b8ec18    // selector: TransferFailed()
    PUSH 0xe0
    SHL
    PUSH 0x80
    MSTORE
    PUSH 0x04
    PUSH 0x80
    REVERT
L175:    // JUMPDEST
    DUP6
    PUSH 0x80
    MSTORE
    DUP4
    PUSH 0xa0
    MSTORE
    DUP3
    PUSH 0xc0
    MSTORE
    PUSH 0xd24ccccf373129a9579bb9f5edc41c09218d54ae950e90b4d5ca2927b7c29b11    // topic: ProtocolFeesCollected(address,uint256,uint256)
    PUSH 0x60
    PUSH 0x80
    LOG1
    DUP4
    PUSH 0x80
    MSTORE
    DUP3
    PUSH 0xa0
    MSTORE
    PUSH 0x40
    PUSH 0x80
    RETURN
    POP
    POP
    POP
    POP
    POP
    POP
    JUMP L2
L176:    // JUMPDEST
    POP
    PUSH 0x04
    CALLDATASIZE
    LT
    ISZERO
    JUMPI L177
    PUSH 0x00
    PUSH 0x00
    REVERT
L177:    // JUMPDEST
    PUSH 0x02
    SLOAD
    PUSH 0x03
    SLOAD
    DUP2
    PUSH 0x80
    MSTORE
    DUP1
    PUSH 0xa0
    MSTORE
    PUSH 0x40
    PUSH 0x80
    RETURN
    POP
    POP
    JUMP L2
L178:    // JUMPDEST
    POP
    PUSH 0x24
    CALLDATASIZE
    LT
    ISZERO
    JUMPI L179
    PUSH 0x00
    PUSH 0x00
    REVERT
L179:    // JUMPDEST
    PUSH 0x04
    CALLDATALOAD
    DUP1
    PUSH 0x00
    MSTORE
    PUSH 0x05
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
    JUMP L2
L180:    // JUMPDEST
    POP
    PUSH 0x04
    CALLDATASIZE
    LT
    ISZERO
    JUMPI L181
    PUSH 0x00
    PUSH 0x00
    REVERT
L181:    // JUMPDEST
    PUSH 0x09
    SLOAD
    PUSH 0x0a
    SLOAD
    DUP2
    PUSH 0x80
    MSTORE
    DUP1
    PUSH 0xa0
    MSTORE
    PUSH 0x40
    PUSH 0x80
    RETURN
    POP
    POP
L2:    // JUMPDEST
