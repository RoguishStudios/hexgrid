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
    Angle, Bearing, Direction, Float, Integer, IntegerSpacing, LineGenIter, LineIter,
    LineIterWithEdgeDetection, LossyLineIter, Position, RangeIter, Ring, Spacing, Spin, Spiral,
};

/// Integer Coordinate on 2d hexagonal grid
///
/// Coordinate Components (Cubic -> Axial):
/// * x -> q
/// * y -> -q - r
/// * z -> r
///
/// ## Hex Orientations
/// ### Flat Topped:
#[doc = include_str!("flat.svg")]
/// ### Pointy Topped:
#[doc = include_str!("pointy.svg")]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
#[derive(Copy, Clone, Default, Eq, PartialEq, Hash, Debug, Ord, PartialOrd)]
pub struct Coordinate<I: Integer = i32> {
    /// `q` coordinate
    pub q: I,
    /// `r` coordinate
    pub r: I,
}

impl<I: Integer> Coordinate<I> {
    /// Create new Coordinate from `q` and `r` axial components.
    ///
    /// See [Hex Coordinates](https://www.redblobgames.com/grids/hexagons/implementation.html#hex)
    pub fn from_axial(q: I, r: I) -> Coordinate<I> {
        Coordinate { q, r }
    }

    /// Create new Coordinate from `x`, `y`, and `z` cubic components.
    ///
    /// See [Hex Coordinates](https://www.redblobgames.com/grids/hexagons/implementation.html#hex)
    pub fn from_cubic(x: I, y: I, z: I) -> Coordinate<I> {
        assert!(x + y + z == I::zero());
        Coordinate { q: x, r: y }
    }

    /// Round position to nearest hex coordinates
    ///
    /// See [Hex Rounding](https://www.redblobgames.com/grids/hexagons/implementation.html#rounding)
    pub fn from_position<F: Float>(position: Position<F>) -> Coordinate<I> {
        let mut q = position.q;
        let mut r = position.r;
        let s = F::zero() - position.q - position.r;

        let q_diff = (q.round() - q).abs();
        let r_diff = (r.round() - r).abs();
        let s_diff = (s.round() - s).abs();

        if q_diff > r_diff && q_diff > s_diff {
            q = F::zero() - r - s;
        } else if r_diff > s_diff {
            r = F::zero() - q - s;
        } else {
            // Not Needed with axial coordinate math
            // s = F::zero() - q - r;
        }

        Coordinate {
            q: I::from(q).unwrap(),
            r: I::from(r).unwrap(),
        }
    }

    /// Round x, y float to nearest hex coordinates.
    ///
    /// Return None, if exactly on the border of two hex coordinates
    pub fn from_position_lossy<F: Float>(position: Position<F>) -> Option<Coordinate<I>> {
        let mut q = position.q;
        let mut r = position.r;
        let s = F::zero() - position.q - position.r;

        let q_diff = (q.round() - q).abs();
        let r_diff = (r.round() - r).abs();
        let s_diff = (s.round() - s).abs();

        if q_diff > r_diff && q_diff > s_diff {
            q = F::zero() - r - s;
        } else if r_diff > s_diff {
            r = F::zero() - q - s;
        } else {
            // Not necessary with axial coordinate math
            // s = F::zero() - q - r;
        }

        if q_diff + r_diff + s_diff > F::from(0.99).unwrap() {
            None
        } else {
            Some(Coordinate {
                q: I::from(q).unwrap(),
                r: I::from(r).unwrap(),
            })
        }
    }

    /// Cubic `X` component.
    pub fn x(&self) -> I {
        self.q
    }

    /// Cubic `Y` component.
    pub fn y(&self) -> I {
        I::zero() - self.q - self.r
    }

    /// Cubic `Z` component.
    pub fn z(&self) -> I {
        self.r
    }

    /// Distance from Origin
    pub fn length(&self) -> I {
        let q = self.q.abs();
        let r = self.r.abs();
        let s = (I::zero() - self.q - self.r).abs();
        (q + r + s) / I::from_u8(2).unwrap()
    }

    /// Convert Coordinate into fractional [Position](crate::Position).
    pub fn into_position<F: Float>(&self) -> Position<F> {
        Position::from_coordinate(*self)
    }

    /// Find the hex containing a pixel. The origin of the pixel coordinates
    /// is the center of the hex at (0,0) in hex coordinates.
    ///

    pub fn from_cartesian<F: Float>(x: F, y: F, spacing: Spacing<F>) -> Coordinate<I> {
        Coordinate::from_position(Position::from_cartesian(x, y, spacing))
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

        let coord = Coordinate { q, r };
        (coord, (qo, ro))
    }

    /// Convert center point to cartesian coordinates using `spacing`, where the size parameter
    /// is the edge length of a hexagon.
    ///
    /// This function is meant for graphical user interfaces where resolution is big enough that
    /// floating point calculation make sense.
    ///
    /// See [Hex to Screen](https://www.redblobgames.com/grids/hexagons/implementation.html#hex-to-pixel)
    pub fn cartesian_center<F: Float>(&self, spacing: Spacing<F>) -> (F, F) {
        let f2: F = F::from(2).unwrap();
        let f3: F = F::from(3).unwrap();
        let f3s: F = f3.sqrt();
        let q: F = F::from(self.q).unwrap();
        let r: F = F::from(self.r).unwrap();

        match spacing {
            Spacing::FlatTop(size) => (size * (f3 / f2 * q), size * (f3s / f2 * q + f3s * r)),
            Spacing::PointyTop(size) => (size * (f3s * q + f3s / f2 * r), size * (f3 / f2 * r)),
        }
    }

    /// Create a set of ordered cartesian points to draw a hex.
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
        let center: (F, F) = self.cartesian_center(spacing);
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
        let q = self.q;
        let r = self.z();
        let two = I::from_i8(2).unwrap();

        match spacing {
            IntegerSpacing::FlatTop(w, h) => (w * q, h * (r + r + q) / two),
            IntegerSpacing::PointyTop(w, h) => (w * (q + q + r) / two, h * r),
        }
    }

    /// Scale coordinate by a factor `scalar`
    ///
    /// See [Coordinate arithmetic](https://www.redblobgames.com/grids/hexagons/implementation.html#hex-arithmetic)
    pub fn scale(&self, scalar: I) -> Coordinate<I> {
        let q = self.q * scalar;
        let r = self.r * scalar;
        Coordinate { q, r }
    }

    /// Array with all the neighbors of a coordinate
    pub fn neighbors(&self) -> [Coordinate<I>; 6] {
        [
            *self + Direction::XZ,
            *self + Direction::XY,
            *self + Direction::ZY,
            *self + Direction::ZX,
            *self + Direction::YX,
            *self + Direction::YZ,
        ]
    }

    /// Rotate self around a point `(0, 0, 0)` using angle of rotation `a`
    pub fn rotate_around_zero(&self, a: Angle) -> Coordinate<I> {
        let (x, y, z) = (self.q, self.r, self.z());

        let (x, y) = match a {
            Angle::Forward => (x, y),
            Angle::RightForward => (-z, -x),
            Angle::RightBackward => (y, z),
            Angle::Backward => (-x, -y),
            Angle::LeftBackward => (z, x),
            Angle::LeftForward => (-y, -z),
        };

        Coordinate { q: x, r: y }
    }

    /// Rotate `self` around a `center` using angle of rotation `a`
    pub fn rotate_around(&self, center: Coordinate<I>, a: Angle) -> Coordinate<I> {
        let rel_p = *self - center;
        let rot_p = rel_p.rotate_around_zero(a);
        rot_p + center
    }

    /// Iterator over each coordinate in straight line from `self` to `dest`
    pub fn line_iter(&self, target: Coordinate<I>) -> LineIter<I> {
        LineIter::new(LineGenIter::new(
            self.into_position(),
            target.into_position(),
        ))
    }

    /// Iterator over each coordinate in straight line from `self` to `dest`
    ///
    /// Skip points on the border of two tiles
    pub fn lossy_line_iter(&self, target: Coordinate<I>) -> LossyLineIter<I> {
        LossyLineIter::new(LineGenIter::new(
            self.into_position(),
            target.into_position(),
        ))
    }

    /// Iterator over each coordinate in straight line from `self` to `dest`
    ///
    /// On edge condition the pair contains different members, otherwise it's the same.
    pub fn line_iter_with_edge_detection(
        &self,
        target: Coordinate<I>,
    ) -> LineIterWithEdgeDetection<I> {
        LineIterWithEdgeDetection::new(LineGenIter::new(
            self.into_position(),
            target.into_position(),
        ))
    }

    /// Direction from center `(0, 0)` to coordinate
    ///
    /// In case of diagonals (edge of two major directions), prefers direction that is clockwise
    /// from the diagonal
    ///
    /// Returns:
    /// None if is center
    ///
    pub fn direction_from_center_cw(&self) -> Option<Direction> {
        let x = self.x();
        let y = self.y();
        let z = self.z();

        let xz = if y < I::zero() { x >= z } else { x > z };
        let zy = if x < I::zero() { z >= y } else { z > y };
        let yx = if z < I::zero() { y >= x } else { y > x };

        match (xz, zy, yx) {
            (true, true, false) => Some(Direction::XZ),
            (true, false, false) => Some(Direction::XY),
            (true, false, true) => Some(Direction::ZY),

            (false, false, true) => Some(Direction::ZX),
            (false, true, true) => Some(Direction::YZ),
            (false, true, false) => Some(Direction::YX),

            (false, false, false) => None,
            (true, true, true) => panic!("You broke math"),
        }
    }

    /// Directions that lead from center to a given point.
    ///
    /// Returns an array of one or two directions.
    pub fn directions_from_center(&self) -> Vec<Direction> {
        let x = self.x();
        let y = self.y();
        let z = self.z();

        let mut dirs = Vec::with_capacity(2);

        if x > I::zero() && z < I::zero() {
            dirs.push(Direction::ZX)
        }

        if x > I::zero() && y < I::zero() {
            dirs.push(Direction::ZY)
        }

        if z > I::zero() && y < I::zero() {
            dirs.push(Direction::XY)
        }

        if z > I::zero() && x < I::zero() {
            dirs.push(Direction::ZX)
        }

        if y > I::zero() && z < I::zero() {
            dirs.push(Direction::YZ)
        }

        if y > I::zero() && x < I::zero() {
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
    /// TODO: Example/Function broken.
    ///
    /// ```notrust
    /// use hexgrid::{Angle, Direction, Coordinate};
    ///
    /// let center = Coordinate::from_axial(0, 0);
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
        let x = self.x();
        let y = self.y();
        let z = self.z();

        let xz = if y > I::zero() { x >= z } else { x > z }; // t
        let zy = if x > I::zero() { z >= y } else { z > y }; // f
        let yx = if z > I::zero() { y >= x } else { y > x }; // f

        match (xz, zy, yx) {
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
        ((self.x() - coordinate.x()).abs()
            + (self.y() - coordinate.y()).abs()
            + (self.z() - coordinate.z()).abs())
            / I::from_i8(2).unwrap()
    }

    /// An iterator over all coordinates in radius `r`
    pub fn range_iter(&self, radius: I) -> RangeIter<I> {
        RangeIter::new(self, radius)
    }

    /// Iterates in a ring around an origin at provided radius.
    ///
    /// Example: Elements in order for Ring of radius 2, Direction YZ, CW
    ///
    #[doc = include_str!("ring.svg")]
    ///
    /// ```
    ///
    /// use hexgrid::{Coordinate, Spin, Direction};
    ///
    /// let center = Coordinate::from_axial(5, -1);
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

    /// Iterates in a spiral around an origin out to the supplied radius.
    ///
    /// Example: Elements in order for all rings from radius 0 to radius 2, Direction ZX, CCW
    ///
    /// ### Ring Iteration Pattern:
    #[doc = include_str!("spiral.svg")]
    /// ```rust
    /// use hexgrid::{Coordinate, Spin, Direction};
    ///
    /// let locations = Coordinate::from_axial(0, 0).spiral_iter(2, Spin::CW(Direction::YZ)).collect::<Vec<_>>();
    ///
    /// assert_eq!(locations.len(), 19);
    /// assert_eq!(locations[0].distance(Coordinate::from_axial(0,0)), 0);
    /// assert_eq!(locations[1].distance(Coordinate::from_axial(0,0)), 1);
    /// assert_eq!(locations[7].distance(Coordinate::from_axial(0,0)), 2);
    ///
    /// ```
    pub fn spiral_iter(&self, radius: I, spin: Spin) -> Spiral<I> {
        Spiral::new(*self, radius, spin)
    }
}

impl<I: Integer> From<(I, I)> for Coordinate<I> {
    fn from(qr: (I, I)) -> Self {
        Coordinate::from_axial(qr.0, qr.1)
    }
}

impl<I: Integer> From<(I, I, I)> for Coordinate<I> {
    fn from(xyz: (I, I, I)) -> Self {
        Coordinate::from_cubic(xyz.0, xyz.1, xyz.2)
    }
}

impl<I: Integer, F: Float> From<Position<F>> for Coordinate<I> {
    fn from(position: Position<F>) -> Self {
        Coordinate::from_position(position)
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
            Direction::YZ => (0, -1),
            Direction::XZ => (1, -1),
            Direction::XY => (1, 0),
            Direction::ZY => (0, 1),
            Direction::ZX => (-1, 1),
            Direction::YX => (-1, 0),
        };

        Coordinate {
            q: I::from_i8(x).unwrap(),
            r: I::from_i8(y).unwrap(),
        }
    }
}

impl<I: Integer, T: Into<Coordinate<I>>> std::ops::Add<T> for Coordinate<I> {
    type Output = Coordinate<I>;

    fn add(self, c: T) -> Coordinate<I> {
        let c: Coordinate<_> = c.into();

        Coordinate {
            q: self.q + c.q,
            r: self.r + c.r,
        }
    }
}

impl<I: Integer, T: Into<Coordinate<I>>> std::ops::Sub<T> for Coordinate<I> {
    type Output = Coordinate<I>;

    fn sub(self, rhs: T) -> Coordinate<I> {
        let c: Coordinate<_> = rhs.into();

        Coordinate {
            q: self.q - c.q,
            r: self.r - c.r,
        }
    }
}

impl<I: Integer> std::ops::Mul<I> for Coordinate<I> {
    type Output = Coordinate<I>;

    fn mul(self, rhs: I) -> Coordinate<I> {
        Coordinate {
            q: self.q * rhs,
            r: self.r * rhs,
        }
    }
}

impl<I: Integer> std::ops::Neg for Coordinate<I> {
    type Output = Coordinate<I>;

    fn neg(self) -> Coordinate<I> {
        Coordinate {
            q: -self.q,
            r: -self.r,
        }
    }
}
