# ssz_serialization
# Copyright (c) 2024 Status Research & Development GmbH
# Licensed and distributed under either of
#   * MIT license (license terms in the root directory or at https://opensource.org/licenses/MIT).
#   * Apache v2 license (license terms in the root directory or at https://www.apache.org/licenses/LICENSE-2.0).
# at your option. This file may not be copied, modified, or distributed except according to those terms.

{.push raises: [].}
{.used.}

import
  std/sequtils,
  results, stew/byteutils, unittest2,
  ../ssz_serialization, ../ssz_serialization/merkleization

type
  # Defines the common merkleization format and a portable serialization format
  Shape {.sszStableContainer: 4.} = object
    side: Opt[uint16]
    color: uint8
    radius: Opt[uint16]

  # Inherits merkleization format from `Shape`, but is serialized more compactly
  Square {.sszVariant: Shape.} = object
    side: uint16
    color: uint8

  # Inherits merkleization format from `Shape`, but is serialized more compactly
  Circle {.sszVariant: Shape.} = object
    radius: uint16
    color: uint8

  ShapeKind {.pure.} = enum
    Square
    Circle

  AnyShape {.sszOneOf: Shape.} = object
    case kind: ShapeKind
    of ShapeKind.Square:
      squareData: Square
    of ShapeKind.Circle:
      circleData: Circle

func selectVariant(value: Shape, circleAllowed = false): Opt[ShapeKind] =
  if value.radius.isSome:
    if not circleAllowed:
      Opt.none ShapeKind
    else:
      Opt.some ShapeKind.Circle
  elif value.side.isSome:
    Opt.some ShapeKind.Square
  else:
    Opt.none ShapeKind

type
  # Defines a container with immutable scheme
  # that contains two `StableContainer`
  ShapePair = object
    shape_1: Shape
    shape_2: Shape

  # Inherits merkleization format from `ShapePair`,
  # and serializes more compactly
  SquarePair {.sszVariant: ShapePair.} = object
    shape_1: Square
    shape_2: Square

  # Inherits merkleization format from `ShapePair`,
  # and reorders fields
  CirclePair {.sszVariant: ShapePair.} = object
    shape_2: Circle
    shape_1: Circle

# Helper containers for merkleization testing
type
  ShapePayload = object
    side: uint16
    color: uint8
    radius: uint16
  ShapeRepr = object
    value: ShapePayload
    active_fields: BitArray[4]

  ShapePairRepr = object
    shape_1: ShapeRepr
    shape_2: ShapeRepr

  AnyShapePair {.sszOneOf: ShapePair.} = object
    case kind: ShapeKind
    of ShapeKind.Square:
      squareData: SquarePair
    of ShapeKind.Circle:
      circleData: CirclePair

func selectVariant(value: ShapePair, circleAllowed = false): Opt[ShapeKind] =
  let
    typ_1 = ? value.shape_1.selectVariant(circleAllowed)
    typ_2 = ? value.shape_2.selectVariant(circleAllowed)
  if typ_1 != typ_2:
    return Opt.none ShapeKind
  Opt.some typ_1

# https://github.com/ethereum/EIPs/blob/master/assets/eip-7495/tests.py
suite "SSZ StableContainer":
  test "Square":
    var
      square_bytes_stable = hexToSeqByte("03420001")
      square_bytes_variant = hexToSeqByte("420001")
      square_root = ShapeRepr(
        value: ShapePayload(side: 0x42, color: 1, radius: 0),
        active_fields: BitArray[4](bytes: [0b0011'u8])).hash_tree_root()
      shapes = @[Shape(side: Opt.some 0x42'u16, color: 1)]
      squares = @[Square(side: 0x42, color: 1)]
    squares.add shapes.mapIt Square.fromVariantBase(it).get
    shapes.add shapes.mapIt Shape(
      side: it.side, color: it.color, radius: it.radius)
    shapes.add squares.mapIt it.toVariantBase()
    squares.add squares.mapIt Square(side: it.side, color: it.color)
    check:
      shapes.toHashSet().card == 1
      squares.toHashSet().card == 1
      shapes.allIt SSZ.encode(it) == square_bytes_stable
      squares.allIt SSZ.encode(it) == square_bytes_variant
      [
        Square.fromVariantBase(SSZ.decode(square_bytes_stable, Shape)).get,
        SSZ.decode(square_bytes_variant, Square),
        AnyShape.fromOneOfBase(
          SSZ.decode(square_bytes_stable, Shape)).get.squareData,
        AnyShape.fromOneOfBase(
          SSZ.decode(square_bytes_stable, Shape),
          circleAllowed = true).get.squareData].toHashSet().card == 1
      shapes.allIt it.hash_tree_root() == square_root
      squares.allIt it.hash_tree_root() == square_root
    static: doAssert not compiles(Circle(side: 0x42, color: 1))
    check:
      shapes.allIt Circle.fromVariantBase(it).isNone
      squares.allIt Circle.fromVariantBase(it.toVariantBase()).isNone
    for shape in shapes.mitems():
      shape.side.ok 0x1337'u16
    for square in squares.mitems():
      square.side = 0x1337
    square_bytes_stable = hexToSeqByte("03371301")
    square_bytes_variant = hexToSeqByte("371301")
    square_root = ShapeRepr(
      value: ShapePayload(side: 0x1337, color: 1, radius: 0),
      active_fields: BitArray[4](bytes: [0b0011'u8])).hash_tree_root()
    check:
      shapes.toHashSet().card == 1
      squares.toHashSet().card == 1
      shapes.allIt SSZ.encode(it) == square_bytes_stable
      squares.allIt SSZ.encode(it) == square_bytes_variant
      [
        Square.fromVariantBase(SSZ.decode(square_bytes_stable, Shape)).get,
        SSZ.decode(square_bytes_variant, Square),
        AnyShape.fromOneOfBase(
          SSZ.decode(square_bytes_stable, Shape)).get.squareData,
        AnyShape.fromOneOfBase(
          SSZ.decode(square_bytes_stable, Shape),
          circleAllowed = true).get.squareData,
      ].toHashSet().card == 1
      shapes.allIt it.hash_tree_root() == square_root
      squares.allIt it.hash_tree_root() == square_root
    for square in squares:
      static: doAssert not compiles(square.radius = 0x1337)
      static: doAssert not compiles(square.side.err())

  test "Circle":
    let
      circle_bytes_stable = hexToSeqByte("06014200")
      circle_bytes_variant = hexToSeqByte("420001")
      circle_root = ShapeRepr(
        value: ShapePayload(side: 0, color: 1, radius: 0x42),
        active_fields: BitArray[4](bytes: [0b0110'u8])).hash_tree_root()
      modified_shape = block:
        var shape = Shape(side: Opt.some 0x42'u16, color: 1)
        shape.side.err()
        shape.radius.ok 0x42'u16
        shape
    var
      shapes = @[Shape(color: 1, radius: Opt.some 0x42'u16), modified_shape]
      circles = @[Circle(radius: 0x42, color: 1)]
    circles.add shapes.mapIt Circle.fromVariantBase(it).get
    shapes.add shapes.mapIt Shape(
      side: it.side, color: it.color, radius: it.radius)
    shapes.add circles.mapIt it.toVariantBase()
    circles.add circles.mapIt Circle(radius: it.radius, color: it.color)
    check:
      shapes.toHashSet().card == 1
      circles.toHashSet().card == 1
      shapes.allIt SSZ.encode(it) == circle_bytes_stable
      circles.allIt SSZ.encode(it) == circle_bytes_variant
      [
        Circle.fromVariantBase(SSZ.decode(circle_bytes_stable, Shape)).get,
        SSZ.decode(circle_bytes_variant, Circle),
        AnyShape.fromOneOfBase(
          SSZ.decode(circle_bytes_stable, Shape),
          circleAllowed = true).get.circleData].toHashSet().card == 1
      shapes.allIt it.hash_tree_root() == circle_root
      circles.allIt it.hash_tree_root() == circle_root
    static: doAssert not compiles(Square(radius: 0x42, color: 1))
    check:
      shapes.allIt Square.fromVariantBase(it).isNone
      circles.allIt Square.fromVariantBase(it.toVariantBase()).isNone
      AnyShape.fromOneOfBase(SSZ.decode(circle_bytes_stable, Shape)).isNone

  test "SquarePair":
    let
      square_pair_bytes_stable =
        hexToSeqByte("080000000c0000000342000103690001")
      square_pair_bytes_variant = hexToSeqByte("420001690001")
      square_pair_root = ShapePairRepr(
        shape_1: ShapeRepr(
          value: ShapePayload(side: 0x42, color: 1, radius: 0),
          active_fields: BitArray[4](bytes: [0b0011'u8])),
        shape_2: ShapeRepr(
          value: ShapePayload(side: 0x69, color: 1, radius: 0),
          active_fields: BitArray[4](bytes: [0b0011'u8]))).hash_tree_root()
    var
      shape_pairs = @[ShapePair(
        shape_1: Shape(side: Opt.some 0x42'u16, color: 1),
        shape_2: Shape(side: Opt.some 0x69'u16, color: 1))]
      square_pairs = @[SquarePair(
        shape_1: Square(side: 0x42, color: 1),
        shape_2: Square(side: 0x69, color: 1))]
    square_pairs.add shape_pairs.mapIt SquarePair.fromVariantBase(it).get
    shape_pairs.add shape_pairs.mapIt(
      ShapePair(shape_1: it.shape_1, shape_2: it.shape_2))
    shape_pairs.add square_pairs.mapIt it.toVariantBase()
    square_pairs.add square_pairs.mapIt(
      SquarePair(shape_1: it.shape_1, shape_2: it.shape_2))
    check:
      shape_pairs.toHashSet().card == 1
      square_pairs.toHashSet().card == 1
      shape_pairs.allIt SSZ.encode(it) == square_pair_bytes_stable
      square_pairs.allIt SSZ.encode(it) == square_pair_bytes_variant
      [
        SquarePair.fromVariantBase(
          SSZ.decode(square_pair_bytes_stable, ShapePair)).get,
        SSZ.decode(square_pair_bytes_variant, SquarePair),
        AnyShapePair.fromOneOfBase(
          SSZ.decode(square_pair_bytes_stable, ShapePair)).get.squareData,
        AnyShapePair.fromOneOfBase(
          SSZ.decode(square_pair_bytes_stable, ShapePair),
          circleAllowed = true).get.squareData].toHashSet().card == 1
      shape_pairs.allIt it.hash_tree_root() == square_pair_root
      square_pairs.allIt it.hash_tree_root() == square_pair_root

  test "CirclePair":
    let
      circle_pair_bytes_stable =
        hexToSeqByte("080000000c0000000601420006016900")
      circle_pair_bytes_variant = hexToSeqByte("690001420001")
      circle_pair_root = ShapePairRepr(
        shape_1: ShapeRepr(
          value: ShapePayload(side: 0, color: 1, radius: 0x42),
          active_fields: BitArray[4](bytes: [0b0110'u8])),
        shape_2: ShapeRepr(
          value: ShapePayload(side: 0, color: 1, radius: 0x69),
          active_fields: BitArray[4](bytes: [0b0110'u8]))).hash_tree_root()
    var
      shape_pairs = @[ShapePair(
        shape_1: Shape(color: 1, radius: Opt.some 0x42'u16),
        shape_2: Shape(color: 1, radius: Opt.some 0x69'u16))]
      circle_pairs = @[CirclePair(
        shape_1: Circle(radius: 0x42, color: 1),
        shape_2: Circle(radius: 0x69, color: 1))]
    circle_pairs.add shape_pairs.mapIt CirclePair.fromVariantBase(it).get
    shape_pairs.add shape_pairs.mapIt(
      ShapePair(shape_1: it.shape_1, shape_2: it.shape_2))
    shape_pairs.add circle_pairs.mapIt it.toVariantBase()
    circle_pairs.add circle_pairs.mapIt(
      CirclePair(shape_1: it.shape_1, shape_2: it.shape_2))
    check:
      shape_pairs.toHashSet().card == 1
      circle_pairs.toHashSet().card == 1
      shape_pairs.allIt SSZ.encode(it) == circle_pair_bytes_stable
      circle_pairs.allIt SSZ.encode(it) == circle_pair_bytes_variant
      [
        CirclePair.fromVariantBase(
          SSZ.decode(circle_pair_bytes_stable, ShapePair)).get,
        SSZ.decode(circle_pair_bytes_variant, CirclePair),
        AnyShapePair.fromOneOfBase(
          SSZ.decode(circle_pair_bytes_stable, ShapePair),
          circleAllowed = true).get.circleData].toHashSet().card == 1
      shape_pairs.allIt it.hash_tree_root() == circle_pair_root
      circle_pairs.allIt it.hash_tree_root() == circle_pair_root

  test "Unsupported (1)":
    let
      shape = Shape(color: 1)
      shape_bytes = hexToSeqByte("0201")
    check:
      SSZ.encode(shape) == shape_bytes
      SSZ.decode(shape_bytes, Shape) == shape
    expect SerializationError:
      discard SSZ.decode(shape_bytes, Square)
    expect SerializationError:
      discard SSZ.decode(shape_bytes, Circle)
    check:
      Square.fromVariantBase(shape).isNone
      Circle.fromVariantBase(shape).isNone
      AnyShape.fromOneOfBase(shape).isNone

  test "Unsupported (2)":
    let
      shape = Shape(
        side: Opt.some 0x42'u16, color: 1, radius: Opt.some 0x42'u16)
      shape_bytes = hexToSeqByte("074200014200")
    check:
      SSZ.encode(shape) == shape_bytes
      SSZ.decode(shape_bytes, Shape) == shape
    expect SerializationError:
      var square: Square
      let stream = unsafeMemoryInput(shape_bytes)
      var reader = init(SszReader, stream)
      reader.readValue(square)
      if stream.readable:
        raise (ref SerializationError)(msg: "Remaining bytes in the input")
    expect SerializationError:
      var circle: Circle
      let stream = unsafeMemoryInput(shape_bytes)
      var reader = init(SszReader, stream)
      reader.readValue(circle)
      if stream.readable:
        raise (ref SerializationError)(msg: "Remaining bytes in the input")
    check:
      Square.fromVariantBase(shape).isNone
      Circle.fromVariantBase(shape).isNone
      AnyShape.fromOneOfBase(shape).isNone

  test "Unsupported (3)":
    expect SerializationError:
      discard SSZ.decode("00", Shape)
    static:
      doAssert not compiles(Square(radius: 0x42, color: 1))
      doAssert not compiles(Circle(side: 0x42, color: 1))

  test "Surrounding container":
    type
      ShapeContainer = object
        shape: Shape
        square: Square
        circle: Circle

      ShapeContainerRepr = object
        shape: ShapeRepr
        square: ShapeRepr
        circle: ShapeRepr

    let
      container = ShapeContainer(
        shape: Shape(
          side: Opt.some 0x42'u16, color: 1, radius: Opt.some 0x42'u16),
        square: Square(side: 0x42, color: 1),
        circle: Circle(radius: 0x42, color: 1))
      container_bytes = hexToSeqByte("0a000000420001420001074200014200")
    check:
      SSZ.encode(container) == container_bytes
      SSZ.decode(container_bytes, ShapeContainer) == container
      container.hash_tree_root == ShapeContainerRepr(
        shape: ShapeRepr(
          value: ShapePayload(side: 0x42, color: 1, radius: 0x42),
          active_fields: BitArray[4](bytes: [0b0111'u8])),
        square: ShapeRepr(
          value: ShapePayload(side: 0x42, color: 1, radius: 0),
          active_fields: BitArray[4](bytes: [0b0011'u8])),
        circle: ShapeRepr(
          value: ShapePayload(side: 0, color: 1, radius: 0x42),
          active_fields: BitArray[4](bytes: [0b0110'u8]))).hash_tree_root()

  test "StableContainer":
    type
      Shape1 {.sszStableContainer: 4.} = object
        side: Opt[uint16]
        color: uint8
        radius: Opt[uint16]

      Shape2 {.sszStableContainer: 8.} = object
        side: Opt[uint16]
        color: uint8
        radius: Opt[uint16]

      Shape3 {.sszStableContainer: 8.} = object
        side: Opt[uint16]
        colors: Opt[List[uint8, Limit 4]]
        radius: Opt[uint16]

    template runTest(value: typed, serialized: string, root: string): untyped =
      block:
        let v = value
        checkpoint $v
        check:
          SSZ.encode(v).toHex() == serialized
          v.hash_tree_root().data.toHex() == root

    runTest(
      value = Shape1(
        side: Opt.some 0x42'u16, color: 1, radius: Opt.some 0x42'u16),
      serialized = "074200014200",
      root = "37b28eab19bc3e246e55d2e2b2027479454c27ee006d92d4847c84893a162e6d")
    runTest(
      value = Shape1(
        side: Opt.some 0x42'u16, color: 1, radius: Opt.none uint16),
      serialized = "03420001",
      root = "bfdb6fda9d02805e640c0f5767b8d1bb9ff4211498a5e2d7c0f36e1b88ce57ff")
    runTest(
      value = Shape1(
        side: Opt.none uint16, color: 1, radius: Opt.none uint16),
      serialized = "0201",
      root = "522edd7309c0041b8eb6a218d756af558e9cf4c816441ec7e6eef42dfa47bb98")
    runTest(
      value = Shape1(
        side: Opt.none uint16, color: 1, radius: Opt.some 0x42'u16),
      serialized = "06014200",
      root = "f66d2c38c8d2afbd409e86c529dff728e9a4208215ca20ee44e49c3d11e145d8")
    runTest(
      value = Shape2(
        side: Opt.some 0x42'u16, color: 1, radius: Opt.some 0x42'u16),
      serialized = "074200014200",
      root = "0792fb509377ee2ff3b953dd9a88eee11ac7566a8df41c6c67a85bc0b53efa4e")
    runTest(
      value = Shape2(
        side: Opt.some 0x42'u16, color: 1, radius: Opt.none uint16),
      serialized = "03420001",
      root = "ddc7acd38ae9d6d6788c14bd7635aeb1d7694768d7e00e1795bb6d328ec14f28")
    runTest(
      value = Shape2(
        side: Opt.none uint16, color: 1, radius: Opt.none uint16),
      serialized = "0201",
      root = "9893ecf9b68030ff23c667a5f2e4a76538a8e2ab48fd060a524888a66fb938c9")
    runTest(
      value = Shape2(
        side: Opt.none uint16, color: 1, radius: Opt.some 0x42'u16),
      serialized = "06014200",
      root = "e823471310312d52aa1135d971a3ed72ba041ade3ec5b5077c17a39d73ab17c5")
    runTest(
      value = Shape3(
        side: Opt.some 0x42'u16,
        colors: Opt.some List[uint8, Limit 4].init @[1'u8, 2],
        radius: Opt.some 0x42'u16),
      serialized = "0742000800000042000102",
      root = "1093b0f1d88b1b2b458196fa860e0df7a7dc1837fe804b95d664279635cb302f")
    runTest(
      value = Shape3(
        side: Opt.some 0x42'u16,
        colors: Opt.none List[uint8, Limit 4],
        radius: Opt.none uint16),
      serialized = "014200",
      root = "28df3f1c3eebd92504401b155c5cfe2f01c0604889e46ed3d22a3091dde1371f")
    runTest(
      value = Shape3(
        side: Opt.none uint16,
        colors: Opt.some List[uint8, Limit 4].init @[1'u8, 2],
        radius: Opt.none uint16),
      serialized = "02040000000102",
      root = "659638368467b2c052ca698fcb65902e9b42ce8e94e1f794dd5296ceac2dec3e")
    runTest(
      value = Shape3(
        side: Opt.none uint16,
        colors: Opt.none List[uint8, Limit 4],
        radius: Opt.some 0x42'u16),
      serialized = "044200",
      root = "d585dd0561c718bf4c29e4c1bd7d4efd4a5fe3c45942a7f778acb78fd0b2a4d2")
    runTest(
      value = Shape3(
        side: Opt.none uint16,
        colors: Opt.some List[uint8, Limit 4].init @[1'u8, 2],
        radius: Opt.some 0x42'u16),
      serialized = "060600000042000102",
      root = "00fc0cecc200a415a07372d5d5b8bc7ce49f52504ed3da0336f80a26d811c7bf")
