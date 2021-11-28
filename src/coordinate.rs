//
// Copyright 2021 Hans W. Uhlig. All Rights Reserved.
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//      http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.
//

use crate::{
    Angle, Bearing, Direction, Float, Integer, IntegerSpacing, LineToGen, LineToIter,
    LineToLossyIter, LineToWithEdgeDetection, Position, RangeIter, Ring, Spacing, Spin, Spiral,
};

/// Integer Coordinate on 2d hexagonal grid
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
#[derive(Copy, Clone, Default, Eq, PartialEq, Hash, Debug, Ord, PartialOrd)]
pub struct Coordinate<I: Integer = i32> {
    /// `x` coordinate
    pub x: I,
    /// `y` coordinate
    pub y: I,
}

impl<I: Integer> Coordinate<I> {
    /// Create new Coord from `x` and `y`
    pub fn from_cubic(x: I, y: I) -> Coordinate<I> {
        Coordinate { x, y }
    }

    /// Convert into fractional position.
    pub fn position<F: Float>(&self) -> Position<F> {
        Position {
            x: F::from(self.x).unwrap(),
            y: F::from(self.y).unwrap(),
        }
    }

    /// Round x, y float to nearest hex coordinates
    pub fn nearest<F: Float>(x: F, y: F) -> Coordinate<I> {
        let zero: F = num::Zero::zero();
        let z: F = zero - x - y;

        let mut rx = x.round();
        let mut ry = y.round();
        let rz = z.round();

        let x_diff = (rx - x).abs();
        let y_diff = (ry - y).abs();
        let z_diff = (rz - z).abs();

        if x_diff > y_diff && x_diff > z_diff {
            rx = -ry - rz;
        } else if y_diff > z_diff {
            ry = -rx - rz;
        } else {
            // not needed, kept for a reference
            // rz = -rx - ry;
        }

        Coordinate {
            x: I::from(rx).unwrap(),
            y: I::from(ry).unwrap(),
        }
    }

    /// Round x, y float to nearest hex coordinates
    ///
    /// Return None, if exactly on the border of two hex coordinates
    pub fn nearest_lossy<F: Float>(x: F, y: F) -> Option<Coordinate<I>> {
        let zero: F = F::zero();
        let z: F = zero - x - y;

        let mut rx = x.round();
        let mut ry = y.round();
        let mut rz = z.round();

        let x_diff = (rx - x).abs();
        let y_diff = (ry - y).abs();
        let z_diff = (rz - z).abs();

        if x_diff > y_diff && x_diff > z_diff {
            rx = -ry - rz;
        } else if y_diff > z_diff {
            ry = -rx - rz;
        } else {
            rz = -rx - ry;
        }

        let x_diff = (rx - x).abs();
        let y_diff = (ry - y).abs();
        let z_diff = (rz - z).abs();

        if x_diff + y_diff + z_diff > F::from(0.99).unwrap() {
            return None;
        }

        Some(Coordinate {
            x: I::from(rx).unwrap(),
            y: I::from(ry).unwrap(),
        })
    }

    /// Find the hex containing a pixel. The origin of the pixel coordinates
    /// is the center of the hex at (0,0) in hex coordinates.
    pub fn from_pixel<F: Float>(x: F, y: F, spacing: Spacing<F>) -> Coordinate<I> {
        let f3: F = F::from(3).unwrap();
        let f2: F = F::from(2).unwrap();
        let f3s: F = f3.sqrt();
        match spacing {
            Spacing::PointyTop(size) => {
                let q = (x * f3s / f3 - y / f3) / size;
                let r = y * f2 / f3 / size;
                Coordinate::nearest(q, -r - q)
            }
            Spacing::FlatTop(size) => {
                let q = x * f2 / f3 / size;
                let r = (-x / f3 + f3s / f3 * y) / size;
                Coordinate::nearest(q, -r - q)
            }
        }
    }

    /// Convert integer pixel coordinates `v` using `spacing` to nearest coordinate that has both
    /// integer pixel coordinates lower or equal to `v`. Also return offset (in integer pixels)
    /// from that coordinate.
    ///
    /// Useful for ASCII visualization. Shamelessly stolen from [Hex2d](https://github.com/dpc/hex2d-rs).
    pub fn nearest_with_offset(spacing: IntegerSpacing<I>, v: (I, I)) -> (Coordinate<I>, (I, I)) {
        let (asc_x, asc_y) = v;

        let two: I = I::from_i8(2).unwrap();

        let ((q, qo), (r, ro)) = match spacing {
            IntegerSpacing::FlatTop(w, h) => (
                (asc_x.div_floor(&w), asc_x.mod_floor(&w)),
                (
                    (asc_y - h * asc_x.div_floor(&w) / two).div_floor(&h),
                    (asc_y + h / two * asc_x.div_floor(&w)).mod_floor(&h),
                ),
            ),
            IntegerSpacing::PointyTop(w, h) => (
                (
                    (asc_x - w * asc_y.div_floor(&h) / two).div_floor(&w),
                    (asc_x + w / two * asc_y.div_floor(&h)).mod_floor(&w),
                ),
                (asc_y.div_floor(&h), asc_y.mod_floor(&h)),
            ),
        };

        let coord = Coordinate { x: q, y: -q - r };
        (coord, (qo, ro))
    }

    /// Convert to pixel coordinates using `spacing`, where the
    /// parameter means the edge length of a hexagon.
    ///
    /// This function is meant for graphical user interfaces
    /// where resolution is big enough that floating point calculation
    /// make sense.
    pub fn to_cartesian_center<F: Float>(&self, spacing: Spacing<F>) -> (F, F) {
        let f3: F = F::from(3).unwrap();
        let f2: F = F::from(2).unwrap();
        let f3s: F = f3.sqrt();
        let q: F = F::from(self.x).unwrap();
        let r: F = F::from(self.z()).unwrap();
        match spacing {
            Spacing::FlatTop(s) => (s * f3 / f2 * q, s * f3s * (r + q / f2)),
            Spacing::PointyTop(s) => (s * f3s * (q + r / f2), s * f3 / f2 * r),
        }
    }

    /// Create a set of ordered points to draw a hex.
    ///
    /// Reference:
    /// [Layout](https://www.redblobgames.com/grids/hexagons/implementation.html#layout)
    /// [Drawing a Hex](https://www.redblobgames.com/grids/hexagons/implementation.html#hex-geometry)
    pub fn to_corner_points<F: Float>(&self, spacing: Spacing<F>) -> [(F, F); 6] {
        let fz: F = F::zero();
        let fh: F = F::from(0.5).unwrap();
        let f2: F = F::from(2).unwrap();
        let f6: F = F::from(6).unwrap();
        let pi: F = F::from(std::f64::consts::PI).unwrap();
        let center: (F, F) = self.to_cartesian_center(spacing);
        let corner_offset = |i| {
            let corner = F::from_u8(i).unwrap();
            let (start_angle, size) = match spacing {
                Spacing::FlatTop(size) => (fz, size),
                Spacing::PointyTop(size) => (fh, size),
            };
            let angle = f2 * pi * (start_angle + corner) / f6;
            (center.0 + size * angle.cos(), center.1 + size * angle.sin())
        };
        [
            corner_offset(0),
            corner_offset(1),
            corner_offset(2),
            corner_offset(3),
            corner_offset(4),
            corner_offset(5),
        ]
    }

    /// Convert to integer pixel coordinates using `spacing`, where the
    /// parameters mean the width and height multiplications
    pub fn to_pixel_integer(&self, spacing: IntegerSpacing<I>) -> (I, I) {
        let q = self.x;
        let r = self.z();
        let two = I::from_i8(2).unwrap();

        match spacing {
            IntegerSpacing::FlatTop(w, h) => (w * q, h * (r + r + q) / two),
            IntegerSpacing::PointyTop(w, h) => (w * (q + q + r) / two, h * r),
        }
    }

    /// Scale coordinate by a factor `s`
    pub fn scale(&self, s: I) -> Coordinate<I> {
        let x = self.x * s;
        let y = self.y * s;
        Coordinate { x, y }
    }

    /// Array with all the neighbors of a coordinate
    pub fn neighbors(&self) -> [Coordinate<I>; 6] {
        [
            *self + Direction::YZ,
            *self + Direction::XZ,
            *self + Direction::XY,
            *self + Direction::ZY,
            *self + Direction::ZX,
            *self + Direction::YX,
        ]
    }

    /// Rotate self around a point `(0, 0, 0)` using angle of rotation `a`
    pub fn rotate_around_zero(&self, a: Angle) -> Coordinate<I> {
        let (x, y, z) = (self.x, self.y, self.z());

        let (x, y) = match a {
            Angle::Forward => (x, y),
            Angle::RightForward => (-z, -x),
            Angle::RightBackward => (y, z),
            Angle::Backward => (-x, -y),
            Angle::LeftBackward => (z, x),
            Angle::LeftForward => (-y, -z),
        };

        Coordinate { x, y }
    }

    /// Rotate `self` around a `center` using angle of rotation `a`
    pub fn rotate_around(&self, center: Coordinate<I>, a: Angle) -> Coordinate<I> {
        let rel_p = *self - center;
        let rot_p = rel_p.rotate_around_zero(a);
        rot_p + center
    }

    fn line_to_iter_gen(&self, dest: Coordinate<I>) -> LineToGen<I> {
        let n = self.distance(dest);

        let ax = self.x.to_f32().unwrap();
        let ay = self.y.to_f32().unwrap();
        let bx = dest.x.to_f32().unwrap();
        let by = dest.y.to_f32().unwrap();
        LineToGen::new(ax, ay, bx, by, n, num::Zero::zero())
    }

    /// Iterator over each coordinate in straight line from `self` to `dest`
    pub fn line_to_iter(&self, dest: Coordinate<I>) -> LineToIter<I> {
        LineToIter::new(self.line_to_iter_gen(dest))
    }

    /// Iterator over each coordinate in straight line from `self` to `dest`
    ///
    /// Skip points on the border of two tiles
    pub fn line_to_lossy_iter(&self, dest: Coordinate<I>) -> LineToLossyIter<I> {
        LineToLossyIter::new(self.line_to_iter_gen(dest))
    }

    /// Iterator over each coordinate in straight line from `self` to `dest`
    ///
    /// On edge condition the pair contains different members, otherwise it's the same.
    pub fn line_to_with_edge_detection_iter(
        &self,
        dest: Coordinate<I>,
    ) -> LineToWithEdgeDetection<I> {
        LineToWithEdgeDetection::new(self.line_to_iter_gen(dest))
    }

    /// Z coordinate
    pub fn z(&self) -> I {
        -self.x - self.y
    }

    /// Direction from center `(0, 0)` to coordinate
    ///
    /// In case of diagonals (edge of two major directions), prefers direction that is clockwise
    /// from the diagonal
    ///
    /// Returns:
    /// None if is center
    ///
    /// ```
    /// use hexgrid::{Angle, Direction, Coordinate};
    ///
    /// let center = Coordinate::from_cubic(0, 0);
    ///
    /// assert_eq!(center.direction_from_center_cw(), None);
    ///
    /// for &d in Direction::all() {
    ///     assert_eq!((center + d).direction_from_center_cw(), Some(d));
    ///     assert_eq!((center + d + (d + Angle::LeftForward)).direction_from_center_cw(), Some(d));
    ///     assert_eq!((center + d + (d + Angle::RightForward)).direction_from_center_cw(), Some(d + Angle::RightForward));
    /// }
    /// ```
    pub fn direction_from_center_cw(&self) -> Option<Direction> {
        let x = self.x;
        let y = self.y;
        let z = self.z();
        let zero: I = I::from_i8(0).unwrap();

        let xy = if z < zero { x >= y } else { x > y };
        let yz = if x < zero { y >= z } else { y > z };
        let zx = if y < zero { z >= x } else { z > x };
        match (xy, yz, zx) {
            (true, true, false) => Some(Direction::XZ),
            (true, false, false) => Some(Direction::XY),
            (true, false, true) => Some(Direction::ZY),

            (false, false, true) => Some(Direction::ZX),
            (false, true, true) => Some(Direction::YX),
            (false, true, false) => Some(Direction::YZ),

            (false, false, false) => None,
            (true, true, true) => panic!("You broke math"),
        }
    }

    /// Directions that lead from center to a given point.
    ///
    /// Returns an array of one or two directions.
    pub fn directions_from_center(&self) -> Vec<Direction> {
        let x = self.x;
        let y = self.y;
        let z = self.z();
        let zero: I = I::from_i8(0).unwrap();

        let mut dirs = Vec::with_capacity(2);

        if x > zero && z < zero {
            dirs.push(Direction::XZ)
        }

        if x > zero && y < zero {
            dirs.push(Direction::XY)
        }

        if z > zero && y < zero {
            dirs.push(Direction::ZY)
        }

        if z > zero && x < zero {
            dirs.push(Direction::ZX)
        }

        if y > zero && z < zero {
            dirs.push(Direction::YZ)
        }

        if y > zero && x < zero {
            dirs.push(Direction::YX)
        }

        dirs
    }

    /// Direction from center `(0, 0)` to coordinate
    ///
    /// In case of diagonals (edge of two major directions), prefers direction that is
    /// counter-clockwise from the diagonal.
    ///
    /// Returns:
    /// None if is center
    ///
    /// ```
    /// use hexgrid::{Angle, Direction, Coordinate};
    ///
    /// let center = Coordinate::from_cubic(0, 0);
    ///
    /// assert_eq!(center.direction_from_center_ccw(), None);
    ///
    /// for &d in Direction::all() {
    ///     assert_eq!((center + d).direction_from_center_ccw(), Some(d));
    ///     assert_eq!((center + d + (d + Angle::LeftForward)).direction_from_center_ccw(), Some(d + Angle::LeftForward));
    ///     assert_eq!((center + d + (d + Angle::RightForward)).direction_from_center_ccw(), Some(d));
    /// }
    /// ```
    pub fn direction_from_center_ccw(&self) -> Option<Direction> {
        let x = self.x;
        let y = self.y;
        let z = self.z();
        let zero: I = I::zero();

        let xy = if z > zero { x >= y } else { x > y };
        let yz = if x > zero { y >= z } else { y > z };
        let zx = if y > zero { z >= x } else { z > x };
        match (xy, yz, zx) {
            (true, true, false) => Some(Direction::XZ),
            (true, false, false) => Some(Direction::XY),
            (true, false, true) => Some(Direction::ZY),

            (false, false, true) => Some(Direction::ZX),
            (false, true, true) => Some(Direction::YX),
            (false, true, false) => Some(Direction::YZ),

            (false, false, false) => None,
            (true, true, true) => panic!("You broke math"),
        }
    }

    /// Directions from self to `coordinate`
    pub fn directions_to(&self, coordinate: Coordinate<I>) -> Vec<Direction> {
        (coordinate - *self).directions_from_center()
    }

    /// Direction from self to `coordinate`
    ///
    /// In case of diagonals (edge of two major directions), prefers direction that is clockwise
    /// from the diagonal.
    ///
    /// Returns:
    /// None if is center
    pub fn direction_to_cw(&self, coordinate: Coordinate<I>) -> Option<Direction> {
        (coordinate - *self).direction_from_center_cw()
    }

    /// Direction from self to `coordinate`
    ///
    /// In case of diagonals (edge of two major directions), prefers direction that is
    /// counter-clockwise from the diagonal.
    ///
    /// Returns:
    /// None if is center
    pub fn direction_to_ccw(&self, coordinate: Coordinate<I>) -> Option<Direction> {
        (coordinate - *self).direction_from_center_ccw()
    }

    /// Distance between two Coordinates
    pub fn distance(&self, coordinate: Coordinate<I>) -> I {
        ((self.x - coordinate.x).abs()
            + (self.y - coordinate.y).abs()
            + (self.z() - coordinate.z()).abs())
            / I::from_i8(2).unwrap()
    }

    /// An iterator over all coordinates in radius `r`
    pub fn range_iter(&self, radius: I) -> RangeIter<I> {
        RangeIter::new(self, radius)
    }

    /// Iterator over each coordinate in a ring
    ///
    /// Example: Elements in order for Ring of radius 2, Direction ZX, CCW
    ///
    /// ```norust
    ///              8
    ///            9   7
    ///         10   .   6
    ///            .   .
    ///         11   x   5
    ///            .   .
    ///          0   .   4
    ///            1   3
    ///              2
    /// ```
    ///
    /// ```
    ///
    /// use hexgrid::{Coordinate, Spin, Direction};
    ///
    /// let center = Coordinate::from_cubic(5, -1);
    ///
    /// for &c in &center.neighbors() {
    ///     for ring_c in c.ring_iter(5, Spin::CCW(Direction::XY)) {
    ///         assert_eq!(c.distance(ring_c), 5);
    ///     }
    /// }
    /// ```
    pub fn ring_iter(&self, radius: I, spin: Spin) -> Ring<I> {
        Ring::new(self, radius, spin)
    }

    /// Iterator over each coordinate in a spiral
    pub fn spiral_iter(&self, radius: I, spin: Spin) -> Spiral<I> {
        Spiral::new(self, radius, spin)
    }
}

impl<I: Integer> From<(I, I)> for Coordinate<I> {
    fn from(xy: (I, I)) -> Self {
        let (x, y) = xy;
        Coordinate { x, y }
    }
}

impl<I: Integer, T: Into<Coordinate<I>>> std::ops::Add<T> for Coordinate<I> {
    type Output = Coordinate<I>;

    fn add(self, c: T) -> Coordinate<I> {
        let c: Coordinate<_> = c.into();

        Coordinate {
            x: self.x + c.x,
            y: self.y + c.y,
        }
    }
}

impl<I: Integer, T: Into<Coordinate<I>>> std::ops::Sub<T> for Coordinate<I> {
    type Output = Coordinate<I>;

    fn sub(self, c: T) -> Coordinate<I> {
        let c: Coordinate<_> = c.into();

        Coordinate {
            x: self.x - c.x,
            y: self.y - c.y,
        }
    }
}

impl<I: Integer> std::ops::Neg for Coordinate<I> {
    type Output = Coordinate<I>;

    fn neg(self) -> Coordinate<I> {
        Coordinate {
            x: -self.x,
            y: -self.y,
        }
    }
}

impl<I: Integer> From<Bearing<I>> for Coordinate<I> {
    fn from(bearing: Bearing<I>) -> Self {
        bearing.coordinate
    }
}

impl<I: Integer> From<Direction> for Coordinate<I> {
    fn from(direction: Direction) -> Self {
        let (x, y) = match direction {
            Direction::YZ => (0, 1),
            Direction::XZ => (1, 0),
            Direction::XY => (1, -1),
            Direction::ZY => (0, -1),
            Direction::ZX => (-1, 0),
            Direction::YX => (-1, 1),
        };

        Coordinate {
            x: I::from_i8(x).unwrap(),
            y: I::from_i8(y).unwrap(),
        }
    }
}
