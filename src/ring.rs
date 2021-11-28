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

use crate::{Angle, Coordinate, Direction, Integer, Spin};
use std::cmp::max;

/// Iterator over a ring
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
#[derive(Copy, Clone, Eq, PartialEq, Hash, Debug, Ord, PartialOrd)]
pub struct Ring<I: Integer> {
    source: Coordinate<I>,
    cur_coord: Coordinate<I>,
    cur_dir: Direction,
    step_angle: Angle,
    r: I,
    ii: I,
    jj: I,
    fuse: bool,
}

impl<I: Integer> Ring<I> {
    pub(crate) fn new(origin: &Coordinate<I>, radius: I, spin: Spin) -> Ring<I> {
        let (start_angle, step_angle, start_dir) = match spin {
            Spin::CW(d) => (
                if radius >= I::zero() {
                    Angle::RightBackward
                } else {
                    Angle::LeftForward
                },
                Angle::RightForward,
                d,
            ),
            Spin::CCW(d) => (
                if radius >= I::zero() {
                    Angle::LeftBackward
                } else {
                    Angle::RightForward
                },
                Angle::LeftForward,
                d,
            ),
        };

        let cur_coord: Coordinate<I> = *origin + Coordinate::from(start_dir).scale(radius);
        let cur_dir = start_dir + start_angle;

        Ring {
            source: origin.clone(),
            cur_coord,
            cur_dir,
            step_angle,
            r: I::abs(&radius),
            ii: I::zero(),
            jj: I::zero(),
            fuse: false,
        }
    }
    /// Get Radius of the `Ring`
    pub fn radius(&self) -> I {
        self.r
    }
}

impl<I: Integer> Iterator for Ring<I> {
    type Item = Coordinate<I>;

    fn next(&mut self) -> Option<Self::Item> {
        if self.fuse {
            return None;
        }
        if self.r.is_zero() {
            self.fuse = true;
            return Some(self.source);
        }

        if self.jj >= self.r.abs() {
            self.ii += I::one();
            if self.ii >= I::from_u8(6).unwrap() {
                self.fuse = true;
                return None;
            }
            self.cur_dir = self.cur_dir + self.step_angle;
            self.jj = I::zero();
        }
        self.jj += I::one();

        let ret = Some(self.cur_coord);
        let cur_dir_coord: Coordinate<_> = self.cur_dir.into();
        self.cur_coord = self.cur_coord + cur_dir_coord;

        ret
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        if self.fuse {
            return (0, Some(0));
        }
        let total_size: usize = if self.r == I::zero() {
            1
        } else {
            I::to_usize(&(self.r * I::from_u8(6).unwrap())).unwrap()
        };
        let past: usize =
            num::ToPrimitive::to_usize(max(&I::zero(), &(self.jj + self.ii * self.r))).unwrap();
        (total_size - past, Some(total_size - past))
    }
}

impl<I: Integer> std::iter::FusedIterator for Ring<I> {}
impl<I: Integer> std::iter::ExactSizeIterator for Ring<I> {}
