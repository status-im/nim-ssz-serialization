# ssz_serialization
# Copyright (c) 2024 Status Research & Development GmbH
# Licensed and distributed under either of
#   * MIT license (license terms in the root directory or at https://opensource.org/licenses/MIT).
#   * Apache v2 license (license terms in the root directory or at https://www.apache.org/licenses/LICENSE-2.0).
# at your option. This file may not be copied, modified, or distributed except according to those terms.

{.push raises: [].}

import
  std/sequtils,
  results, stew/byteutils, unittest2,
  ../ssz_serialization, ../ssz_serialization/merkleization

type
  # Defines the common merkleization format and a portable serialization format
  # across variants
  Shape* {.sszStableContainer: 4.} = object
    side*: Opt[uint16]
    color*: uint8
    radius*: Opt[uint16]

  # Inherits merkleization format from `Shape`, but is serialized more compactly
  Square* {.sszVariant: Shape.} = object
    side*: uint16
    color*: uint8

  # Inherits merkleization format from `Shape`, but is serialized more compactly
  Circle* {.sszVariant: Shape.} = object
    radius*: uint16
    color*: uint8

  ShapeKind {.pure.} = enum
    Square
    Circle

  AnyShape {.sszOneOf: Shape.} = object
    case kind: ShapeKind
    of ShapeKind.Square:
      squareData: Square
    of ShapeKind.Circle:
      circleData: Circle

func selectVariant*(value: Shape, circleAllowed = false): Opt[ShapeKind] =
  if value.radius.isSome:
    if not circleAllowed:
      Opt.none ShapeKind
    else:
      Opt.some ShapeKind.Circle
  elif value.side.isSome:
    Opt.some ShapeKind.Square
  else:
    Opt.none ShapeKind

# Helper containers for merkleization testing
type
  ShapePayload = object
    side: uint16
    color: uint8
    radius: uint16
  ShapeRepr = object
    value: ShapePayload
    active_fields: BitArray[4]

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
      discard SSZ.decode(shape_bytes, Square)
    expect SerializationError:
      discard SSZ.decode(shape_bytes, Circle)
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
