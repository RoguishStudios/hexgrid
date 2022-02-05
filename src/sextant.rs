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

use crate::{Coordinate, Integer};

///
/// Which slice of a hexgrid does a coordinate exist in.
///
/// ### Flat Topped:
#[doc = include_str!("flat.svg")]
/// ### Pointy Topped:
#[doc = include_str!("pointy.svg")]
#[derive(Debug, Ord, PartialOrd, Eq, PartialEq, Copy, Clone, Hash)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub enum Sextant {
    /// YZ Sextant
    YZ,
    /// XZ Sextant
    XZ,
    /// XY Sextant
    XY,
    /// ZY Sextant
    ZY,
    /// ZX Sextant
    ZX,
    /// YX Sextant
    YX,
}

impl<I: Integer> From<Coordinate<I>> for Sextant {
    fn from(coordinate: Coordinate<I>) -> Self {
        match (
            coordinate.x() >= I::zero(),
            coordinate.y() >= I::zero(),
            coordinate.z() >= I::zero(),
        ) {
            (true, false, true) => Sextant::YZ,
            (true, false, false) => Sextant::XZ,
            (true, true, false) => Sextant::XY,
            (false, true, false) => Sextant::ZY,
            (false, true, true) => Sextant::ZX,
            (false, false, true) => Sextant::YX,
            _ => panic!("You Broke Math"),
        }
    }
}
