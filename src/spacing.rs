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

/// Floating point tile size for pixel conversion functions
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
#[derive(Copy, Clone, PartialEq, Debug, PartialOrd)]
pub enum Spacing<F: Float = f32> {
    /// Hex-grid with an edge on top
    FlatTop(F),
    /// Hex-grid with a corner on top
    PointyTop(F),
}

/// Integer pixel tile size for integer pixel conversion functions
///
/// Example values that give good results:
///
/// * FlatTop(3, 2)
/// * PointyTop(2, 1)
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
#[derive(Copy, Clone, Eq, PartialEq, Debug, Hash, Ord, PartialOrd)]
pub enum IntegerSpacing<I: Integer> {
    /// Hex-grid with an edge on top
    FlatTop(I, I),
    /// Hex-grid with a corner on top
    PointyTop(I, I),
}
