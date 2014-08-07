var list
var ver
var verbody

function real_init () {
  list = document.getElementById("thelist")
  ver = document.getElementById("thever")

/* expects "thelist" to contain some DIV nodes (and other things);
   each DIV node should contain at least two DIV nodes, the first of which is
   treated as a header that can be clicked on, and the second of which
   is the entity that appears or disappears on clicking.
*/
  for (var i = 0; i < list.childNodes.length; i++) {
    var n = list.childNodes[i]
    if (String(n.tagName).toLowerCase() != "div") {
      continue
    }
    for (var j = 0; j < n.childNodes.length; j++) {
      var nn = n.childNodes[j]
      if (String(nn.tagName).toLowerCase() == "div") {
        nn.style.background = "#ffffc0"
        for (var k = j+1; k < n.childNodes.length; k++) {
          var nnn = n.childNodes[k]
          if (String(nnn.tagName).toLowerCase() == "div") {
            nnn.style.display = "none"
            break
          }
        }
        // should really warn if no DIV child...
        nn.setAttribute("onclick","openclose("+i+","+k+")")
        break
      }
    }
  }
/* expects "ver" to contain a DIV node */
  for (var i = 0; i < ver.childNodes.length; i++) {
    var n = ver.childNodes[i];
    if (String(n.tagName).toLowerCase() == "div") {
      verbody = n
      verbody.style.display = "none"
      ver.setAttribute("onclick","openclosever()")
      break
    }
  }
}

function openclose (i,k) {
  n = list.childNodes[i].childNodes[k]
  if (n.style.display == "none") {
    n.style.display = ""
  } else {
    n.style.display = "none"
  }
}

function openclosevcs () {
/* expects the style sheet to have rules on div.newvars pre and
   div.newcons pre; toggles their display status.
*/
  rules = document.styleSheets[0].cssRules
  for (var i = 0; i < rules.length; i++) {
    var rule = rules[i]
    if (rule.type == CSSRule.STYLE_RULE
        && rule.selectorText.match(/^div.new(?:vars|cons) pre$/i)) {
      rule.style.setProperty("display",
        (rule.style.getPropertyValue("display") == "none") ? "" : "none","")
    }
  }
}

function openclosever () {
  if (verbody.style.display == "none") {
    verbody.style.display = ""
  } else {
    verbody.style.display = "none"
  }
}

window.onload = real_init;

function init () {
  /* dummy for end-of-page hook */
}
