(function() {var implementors = {};
implementors["hexgrid"] = [{"text":"impl <a class=\"trait\" href=\"serde/ser/trait.Serialize.html\" title=\"trait serde::ser::Serialize\">Serialize</a> for <a class=\"enum\" href=\"hexgrid/enum.Angle.html\" title=\"enum hexgrid::Angle\">Angle</a>","synthetic":false,"types":["hexgrid::angle::Angle"]},{"text":"impl&lt;I:&nbsp;<a class=\"trait\" href=\"hexgrid/trait.Integer.html\" title=\"trait hexgrid::Integer\">Integer</a>&gt; <a class=\"trait\" href=\"serde/ser/trait.Serialize.html\" title=\"trait serde::ser::Serialize\">Serialize</a> for <a class=\"struct\" href=\"hexgrid/struct.Bearing.html\" title=\"struct hexgrid::Bearing\">Bearing</a>&lt;I&gt; <span class=\"where fmt-newline\">where<br>&nbsp;&nbsp;&nbsp;&nbsp;I: <a class=\"trait\" href=\"serde/ser/trait.Serialize.html\" title=\"trait serde::ser::Serialize\">Serialize</a>,&nbsp;</span>","synthetic":false,"types":["hexgrid::bearing::Bearing"]},{"text":"impl&lt;I:&nbsp;<a class=\"trait\" href=\"hexgrid/trait.Integer.html\" title=\"trait hexgrid::Integer\">Integer</a>&gt; <a class=\"trait\" href=\"serde/ser/trait.Serialize.html\" title=\"trait serde::ser::Serialize\">Serialize</a> for <a class=\"struct\" href=\"hexgrid/struct.Coordinate.html\" title=\"struct hexgrid::Coordinate\">Coordinate</a>&lt;I&gt; <span class=\"where fmt-newline\">where<br>&nbsp;&nbsp;&nbsp;&nbsp;I: <a class=\"trait\" href=\"serde/ser/trait.Serialize.html\" title=\"trait serde::ser::Serialize\">Serialize</a>,&nbsp;</span>","synthetic":false,"types":["hexgrid::coordinate::Coordinate"]},{"text":"impl <a class=\"trait\" href=\"serde/ser/trait.Serialize.html\" title=\"trait serde::ser::Serialize\">Serialize</a> for <a class=\"enum\" href=\"hexgrid/enum.Direction.html\" title=\"enum hexgrid::Direction\">Direction</a>","synthetic":false,"types":["hexgrid::direction::Direction"]},{"text":"impl&lt;I:&nbsp;<a class=\"trait\" href=\"hexgrid/trait.Integer.html\" title=\"trait hexgrid::Integer\">Integer</a>, F:&nbsp;<a class=\"trait\" href=\"hexgrid/trait.Float.html\" title=\"trait hexgrid::Float\">Float</a>&gt; <a class=\"trait\" href=\"serde/ser/trait.Serialize.html\" title=\"trait serde::ser::Serialize\">Serialize</a> for <a class=\"struct\" href=\"hexgrid/struct.LineGenIter.html\" title=\"struct hexgrid::LineGenIter\">LineGenIter</a>&lt;I, F&gt; <span class=\"where fmt-newline\">where<br>&nbsp;&nbsp;&nbsp;&nbsp;I: <a class=\"trait\" href=\"serde/ser/trait.Serialize.html\" title=\"trait serde::ser::Serialize\">Serialize</a>,<br>&nbsp;&nbsp;&nbsp;&nbsp;F: <a class=\"trait\" href=\"serde/ser/trait.Serialize.html\" title=\"trait serde::ser::Serialize\">Serialize</a>,&nbsp;</span>","synthetic":false,"types":["hexgrid::line::LineGenIter"]},{"text":"impl&lt;I:&nbsp;<a class=\"trait\" href=\"hexgrid/trait.Integer.html\" title=\"trait hexgrid::Integer\">Integer</a>, F:&nbsp;<a class=\"trait\" href=\"hexgrid/trait.Float.html\" title=\"trait hexgrid::Float\">Float</a>&gt; <a class=\"trait\" href=\"serde/ser/trait.Serialize.html\" title=\"trait serde::ser::Serialize\">Serialize</a> for <a class=\"struct\" href=\"hexgrid/struct.LineIter.html\" title=\"struct hexgrid::LineIter\">LineIter</a>&lt;I, F&gt; <span class=\"where fmt-newline\">where<br>&nbsp;&nbsp;&nbsp;&nbsp;I: <a class=\"trait\" href=\"serde/ser/trait.Serialize.html\" title=\"trait serde::ser::Serialize\">Serialize</a>,<br>&nbsp;&nbsp;&nbsp;&nbsp;F: <a class=\"trait\" href=\"serde/ser/trait.Serialize.html\" title=\"trait serde::ser::Serialize\">Serialize</a>,&nbsp;</span>","synthetic":false,"types":["hexgrid::line::LineIter"]},{"text":"impl&lt;I:&nbsp;<a class=\"trait\" href=\"hexgrid/trait.Integer.html\" title=\"trait hexgrid::Integer\">Integer</a>, F:&nbsp;<a class=\"trait\" href=\"hexgrid/trait.Float.html\" title=\"trait hexgrid::Float\">Float</a>&gt; <a class=\"trait\" href=\"serde/ser/trait.Serialize.html\" title=\"trait serde::ser::Serialize\">Serialize</a> for <a class=\"struct\" href=\"hexgrid/struct.LossyLineIter.html\" title=\"struct hexgrid::LossyLineIter\">LossyLineIter</a>&lt;I, F&gt; <span class=\"where fmt-newline\">where<br>&nbsp;&nbsp;&nbsp;&nbsp;I: <a class=\"trait\" href=\"serde/ser/trait.Serialize.html\" title=\"trait serde::ser::Serialize\">Serialize</a>,<br>&nbsp;&nbsp;&nbsp;&nbsp;F: <a class=\"trait\" href=\"serde/ser/trait.Serialize.html\" title=\"trait serde::ser::Serialize\">Serialize</a>,&nbsp;</span>","synthetic":false,"types":["hexgrid::line::LossyLineIter"]},{"text":"impl&lt;I:&nbsp;<a class=\"trait\" href=\"hexgrid/trait.Integer.html\" title=\"trait hexgrid::Integer\">Integer</a>, F:&nbsp;<a class=\"trait\" href=\"hexgrid/trait.Float.html\" title=\"trait hexgrid::Float\">Float</a>&gt; <a class=\"trait\" href=\"serde/ser/trait.Serialize.html\" title=\"trait serde::ser::Serialize\">Serialize</a> for <a class=\"struct\" href=\"hexgrid/struct.LineIterWithEdgeDetection.html\" title=\"struct hexgrid::LineIterWithEdgeDetection\">LineIterWithEdgeDetection</a>&lt;I, F&gt; <span class=\"where fmt-newline\">where<br>&nbsp;&nbsp;&nbsp;&nbsp;I: <a class=\"trait\" href=\"serde/ser/trait.Serialize.html\" title=\"trait serde::ser::Serialize\">Serialize</a>,<br>&nbsp;&nbsp;&nbsp;&nbsp;F: <a class=\"trait\" href=\"serde/ser/trait.Serialize.html\" title=\"trait serde::ser::Serialize\">Serialize</a>,&nbsp;</span>","synthetic":false,"types":["hexgrid::line::LineIterWithEdgeDetection"]},{"text":"impl&lt;N&gt; <a class=\"trait\" href=\"serde/ser/trait.Serialize.html\" title=\"trait serde::ser::Serialize\">Serialize</a> for <a class=\"struct\" href=\"hexgrid/struct.Offset.html\" title=\"struct hexgrid::Offset\">Offset</a>&lt;N&gt; <span class=\"where fmt-newline\">where<br>&nbsp;&nbsp;&nbsp;&nbsp;N: <a class=\"trait\" href=\"serde/ser/trait.Serialize.html\" title=\"trait serde::ser::Serialize\">Serialize</a>,&nbsp;</span>","synthetic":false,"types":["hexgrid::offset::Offset"]},{"text":"impl&lt;F:&nbsp;<a class=\"trait\" href=\"hexgrid/trait.Float.html\" title=\"trait hexgrid::Float\">Float</a>&gt; <a class=\"trait\" href=\"serde/ser/trait.Serialize.html\" title=\"trait serde::ser::Serialize\">Serialize</a> for <a class=\"struct\" href=\"hexgrid/struct.Position.html\" title=\"struct hexgrid::Position\">Position</a>&lt;F&gt; <span class=\"where fmt-newline\">where<br>&nbsp;&nbsp;&nbsp;&nbsp;F: <a class=\"trait\" href=\"serde/ser/trait.Serialize.html\" title=\"trait serde::ser::Serialize\">Serialize</a>,&nbsp;</span>","synthetic":false,"types":["hexgrid::position::Position"]},{"text":"impl&lt;I:&nbsp;<a class=\"trait\" href=\"hexgrid/trait.Integer.html\" title=\"trait hexgrid::Integer\">Integer</a>&gt; <a class=\"trait\" href=\"serde/ser/trait.Serialize.html\" title=\"trait serde::ser::Serialize\">Serialize</a> for <a class=\"struct\" href=\"hexgrid/struct.RangeIter.html\" title=\"struct hexgrid::RangeIter\">RangeIter</a>&lt;I&gt; <span class=\"where fmt-newline\">where<br>&nbsp;&nbsp;&nbsp;&nbsp;I: <a class=\"trait\" href=\"serde/ser/trait.Serialize.html\" title=\"trait serde::ser::Serialize\">Serialize</a>,&nbsp;</span>","synthetic":false,"types":["hexgrid::range::RangeIter"]},{"text":"impl&lt;I:&nbsp;<a class=\"trait\" href=\"hexgrid/trait.Integer.html\" title=\"trait hexgrid::Integer\">Integer</a>&gt; <a class=\"trait\" href=\"serde/ser/trait.Serialize.html\" title=\"trait serde::ser::Serialize\">Serialize</a> for <a class=\"struct\" href=\"hexgrid/struct.Ring.html\" title=\"struct hexgrid::Ring\">Ring</a>&lt;I&gt; <span class=\"where fmt-newline\">where<br>&nbsp;&nbsp;&nbsp;&nbsp;I: <a class=\"trait\" href=\"serde/ser/trait.Serialize.html\" title=\"trait serde::ser::Serialize\">Serialize</a>,&nbsp;</span>","synthetic":false,"types":["hexgrid::ring::Ring"]},{"text":"impl <a class=\"trait\" href=\"serde/ser/trait.Serialize.html\" title=\"trait serde::ser::Serialize\">Serialize</a> for <a class=\"enum\" href=\"hexgrid/enum.Sextant.html\" title=\"enum hexgrid::Sextant\">Sextant</a>","synthetic":false,"types":["hexgrid::sextant::Sextant"]},{"text":"impl&lt;F:&nbsp;<a class=\"trait\" href=\"hexgrid/trait.Float.html\" title=\"trait hexgrid::Float\">Float</a>&gt; <a class=\"trait\" href=\"serde/ser/trait.Serialize.html\" title=\"trait serde::ser::Serialize\">Serialize</a> for <a class=\"enum\" href=\"hexgrid/enum.Spacing.html\" title=\"enum hexgrid::Spacing\">Spacing</a>&lt;F&gt; <span class=\"where fmt-newline\">where<br>&nbsp;&nbsp;&nbsp;&nbsp;F: <a class=\"trait\" href=\"serde/ser/trait.Serialize.html\" title=\"trait serde::ser::Serialize\">Serialize</a>,&nbsp;</span>","synthetic":false,"types":["hexgrid::spacing::Spacing"]},{"text":"impl&lt;I:&nbsp;<a class=\"trait\" href=\"hexgrid/trait.Integer.html\" title=\"trait hexgrid::Integer\">Integer</a>&gt; <a class=\"trait\" href=\"serde/ser/trait.Serialize.html\" title=\"trait serde::ser::Serialize\">Serialize</a> for <a class=\"enum\" href=\"hexgrid/enum.IntegerSpacing.html\" title=\"enum hexgrid::IntegerSpacing\">IntegerSpacing</a>&lt;I&gt; <span class=\"where fmt-newline\">where<br>&nbsp;&nbsp;&nbsp;&nbsp;I: <a class=\"trait\" href=\"serde/ser/trait.Serialize.html\" title=\"trait serde::ser::Serialize\">Serialize</a>,&nbsp;</span>","synthetic":false,"types":["hexgrid::spacing::IntegerSpacing"]},{"text":"impl <a class=\"trait\" href=\"serde/ser/trait.Serialize.html\" title=\"trait serde::ser::Serialize\">Serialize</a> for <a class=\"enum\" href=\"hexgrid/enum.Spin.html\" title=\"enum hexgrid::Spin\">Spin</a>","synthetic":false,"types":["hexgrid::spin::Spin"]},{"text":"impl&lt;I:&nbsp;<a class=\"trait\" href=\"hexgrid/trait.Integer.html\" title=\"trait hexgrid::Integer\">Integer</a>&gt; <a class=\"trait\" href=\"serde/ser/trait.Serialize.html\" title=\"trait serde::ser::Serialize\">Serialize</a> for <a class=\"struct\" href=\"hexgrid/struct.Spiral.html\" title=\"struct hexgrid::Spiral\">Spiral</a>&lt;I&gt; <span class=\"where fmt-newline\">where<br>&nbsp;&nbsp;&nbsp;&nbsp;I: <a class=\"trait\" href=\"serde/ser/trait.Serialize.html\" title=\"trait serde::ser::Serialize\">Serialize</a>,&nbsp;</span>","synthetic":false,"types":["hexgrid::spiral::Spiral"]}];
if (window.register_implementors) {window.register_implementors(implementors);} else {window.pending_implementors = implementors;}})()