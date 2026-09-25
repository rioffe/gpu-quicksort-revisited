-- docs/repo-links.lua -- rewrite the article's relative links (written for GitHub's view of
-- docs/ARTICLE.md, e.g. ../SPEC.md or ARCHITECTURE.md) to absolute links into the repository,
-- so they still work from the published page at rioffe.github.io/gpu-quicksort-revisited/.
local REPO = "https://github.com/rioffe/gpu-quicksort-revisited/blob/main/"

-- Resolve `path` against docs/ and normalize "." and ".." segments.
local function resolve(path)
  local parts = { "docs" }
  for seg in path:gmatch("[^/]+") do
    if seg == ".." then table.remove(parts)
    elseif seg ~= "." then table.insert(parts, seg) end
  end
  return table.concat(parts, "/")
end

function Link(el)
  local t = el.target
  if t:match("^%a[%w+.-]*:") or t:match("^#") or t:match("^/") then return nil end
  el.target = REPO .. resolve(t)
  return el
end
