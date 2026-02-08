/-
Security test module for SBS-Test.
Tests XSS prevention in user-controlled fields.

This module contains intentionally malicious-looking inputs to verify
that the HTML escaping works correctly. If the build succeeds and the
rendered output shows escaped text (not executing scripts), the security
hardening is working.
-/
import Dress
import Mathlib.Tactic

namespace SBSTest.SecurityTest

/-! ## XSS Attack Vector Tests

Each theorem below tests a different user-controlled field with potentially
malicious content. The expected behavior is that all special characters
are HTML-escaped in the output.
-/

-- Test 1: XSS in title field
@[blueprint "xss_title"
  (title := "<script>alert('XSS in title')</script>")
  (message := "Testing XSS in title field")
  (statement := /-- Security test: title field with script tag. -/)
  (proof := /-- Immediate by the constructor of `True`. -/)]
theorem xss_title : True := trivial

-- Test 2: XSS in message field
@[blueprint "xss_message"
  (title := "XSS Message Test")
  (message := "<img src=x onerror=alert('XSS')>")
  (statement := /-- Security test: message field with img tag. -/)
  (proof := /-- Trivially true by applying `True.intro`. -/)]
theorem xss_message : True := trivial

-- Test 3: XSS in blocked field
@[blueprint "xss_blocked"
  (title := "XSS Blocked Test")
  (blocked := "<svg onload=alert('XSS')>")
  (statement := /-- Security test: blocked field with svg tag. -/)
  (proof := /-- The goal `True` is closed directly by its unique constructor. -/)]
theorem xss_blocked : True := trivial

-- Test 4: XSS in potentialIssue field
@[blueprint "xss_issue"
  (title := "XSS Issue Test")
  (potentialIssue := "<iframe src=javascript:alert('XSS')>")
  (statement := /-- Security test: potentialIssue with iframe. -/)
  (proof := /-- Follows immediately from the `trivial` tactic, which applies `True.intro`. -/)]
theorem xss_issue : True := trivial

-- Test 5: XSS in technicalDebt field
@[blueprint "xss_debt"
  (title := "XSS Debt Test")
  (technicalDebt := "onclick=alert('XSS') style=\"background:red\"")
  (statement := /-- Security test: technicalDebt with event handler. -/)
  (proof := /-- Solved by the `trivial` tactic, which dispatches `True` via its constructor. -/)]
theorem xss_debt : True := trivial

-- Test 6: XSS in misc field
@[blueprint "xss_misc"
  (title := "XSS Misc Test")
  (misc := "<a href=\"javascript:alert('XSS')\">click</a>")
  (statement := /-- Security test: misc field with javascript URL. -/)
  (proof := /-- Immediate: `True` has a single constructor and `trivial` applies it. -/)]
theorem xss_misc : True := trivial

-- Test 7: HTML entities in displayNumber (via title shown as label)
@[blueprint "xss_label"
  (title := "&lt;script&gt; already escaped & more <script>not escaped</script>")
  (statement := /-- Security test: mix of escaped and unescaped HTML. -/)
  (proof := /-- The proposition `True` is proved by its sole constructor `True.intro`. -/)]
theorem xss_label : True := trivial

-- Test 8: Quote injection in attributes
@[blueprint "xss_quotes"
  (title := "Test\" onclick=\"alert('XSS')\" data-x=\"")
  (message := "Testing quote escaping in HTML attributes")
  (statement := /-- Security test: quote injection attack. -/)
  (proof := /-- Trivially discharged: `trivial` closes any `True` goal. -/)]
theorem xss_quotes : True := trivial

end SBSTest.SecurityTest
