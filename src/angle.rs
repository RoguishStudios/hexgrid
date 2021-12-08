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

use crate::{Float, Integer};

/// Angle, relative to a Direction
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
#[derive(Copy, Clone, Eq, PartialEq, Hash, Debug, Ord, PartialOrd)]
pub enum Angle {
    /// 0-deg clockwise
    Forward,
    /// 60-deg clockwise
    RightForward,
    /// 120-deg clockwise
    RightBackward,
    /// 180-deg clockwise
    Backward,
    /// 240-deg clockwise
    LeftBackward,
    /// 300-deg clockwise
    LeftForward,
}

impl Angle {
    /// Static array of all angles
    ///
    /// ```
    /// use hexgrid::Angle;
    ///
    /// assert_eq!(Angle::all().len(), 6);
    /// ```
    pub fn all() -> &'static [Angle; 6] {
        &[
            Angle::Forward,
            Angle::RightForward,
            Angle::RightBackward,
            Angle::Backward,
            Angle::LeftBackward,
            Angle::LeftForward,
        ]
    }

    /// Create Angle from integer ordinal in [0, 6) range.
    pub fn from_int<I: Integer>(i: I) -> Angle {
        match i.mod_floor(&I::from_u8(6).unwrap()).to_u8().unwrap() {
            0 => Angle::Forward,
            1 => Angle::RightForward,
            2 => Angle::RightBackward,
            3 => Angle::Backward,
            4 => Angle::LeftBackward,
            5 => Angle::LeftForward,
            _ => panic!(),
        }
    }

    /// Convert angle to integer ordinal in [0, 6) range.
    pub fn to_int<I: Integer>(&self) -> I {
        I::from_u8(*self as u8).unwrap()
    }

    /// Convert to degrees from bearing.
    pub fn to_degree<F: Float>(&self) -> F {
        match self {
            Angle::Forward => F::from(0.0).unwrap(),
            Angle::RightForward => F::from(60.0).unwrap(),
            Angle::RightBackward => F::from(120.0).unwrap(),
            Angle::Backward => F::from(180.0).unwrap(),
            Angle::LeftBackward => F::from(240.0).unwrap(),
            Angle::LeftForward => F::from(300.0).unwrap(),
        }
    }
}
