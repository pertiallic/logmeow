
Props = {"succ", "add", "mul", "proj1", "proj2", "input", "print", "eq", "le", "lt", "isnat", "ispair"}

local function tobinary(num)
    if num == 0 then
        return "0"
    end
    local bits = {}
    local n = num
    while n > 1 do
        table.insert(bits, 1, tostring(n % 2))
        n = n >> 1
    end
    if n == 1 then
        table.insert(bits, 1, "1")
    end
    return table.concat(bits, "")
end

local function transpile_w(prog)
    local initial = prog:gsub( "\\%s*", ""):gsub("にゃ", "1"):gsub("ん", "|"):gsub("ー", "0")
    local lines = {}
    for w in string.gmatch(initial, "[^\n]+") do
        table.insert(lines, w)
    end
    local out = {}
    for _, w in ipairs(lines) do
        local line = {}
        for u in string.gmatch(w, "[01]+") do
            if u == "1" then
                local r = table.remove(line)
                local l = table.remove(line)
                if string.match(r, "^%[") then
                    table.insert(line, "["..l..", "..string.sub(r, 2))
                else
                    table.insert(line, "["..l..", "..r.."]")
                end
            elseif u == "10" then
                table.insert(line, "or")
            elseif string.match(u, "^101") then
                local id = tonumber(string.sub(u, 3), 2)
                table.insert(line, "_"..id)
            elseif string.match(u, "^1001") then
                local id = tonumber(string.sub(u, 4), 2)
                table.insert(line, Props[id])
            elseif string.match(u, "^10001") then
                local id = tonumber(string.sub(u, 5), 2)
                table.insert(line, "P"..id)
            elseif string.match(u, "^11") then
                local num = tonumber(string.sub(u, 4), 2)
                if "1" == string.sub(u, 3, 3) then num = -num end
                table.insert(line, tostring(num))
            end
        end
        table.insert(out, table.concat(line, " "))
    end
    return table.concat(out, "\n")
end

local function transpile_r(prog)
    local lines = {}
    for l in string.gmatch(prog:gsub(",", " , "):gsub("%[", " [ "):gsub("%]", " ] "), "[^\n]+") do
        table.insert(lines, l)
    end
    local out = {}
    for _, w in ipairs(lines) do
        local line = {}
        local pairs = {}
        for u in string.gmatch(w,"[^%s]+") do
            local add = ""
            if u == "," then
                --pass
                goto continue
            elseif u == "[" then
                table.insert(pairs, {})
                goto continue
            elseif u == "]" then
                local l = table.remove(pairs)
                add = table.concat(l) .. string.rep("にゃん", #l - 1)
            elseif u == "or" then
                add = "にゃーん"
            elseif string.match(u, "^_[0-9]+") then
                local id = assert(tonumber(string.sub(u, 2)))
                add = "にゃー" .. tobinary(id):gsub("1", "にゃ"):gsub("0", "ー") .. "ん"
            elseif string.match(u, "^P[0-9]+") then
                local id = tonumber(string.sub(u, 2))
                add = "にゃーーー" .. tobinary(id):gsub("1", "にゃ"):gsub("0", "ー") .. "ん"
            elseif string.match(u, "^%-?[0-9]+") then
                local num = tonumber(string.sub(u, 1))
                if num < 0 then
                    add = "にゃにゃにゃ" .. tobinary(-num):gsub("1", "にゃ"):gsub("0", "ー") .. "ん"
                else
                    add = "にゃにゃー" .. tobinary(num):gsub("1", "にゃ"):gsub("0", "ー") .. "ん"
                end
            else
                local id = 0
                for j, p in ipairs(Props) do
                    if p == u then
                        id = j
                        break
                    end
                end
                assert(id ~= 0, "transpile_r: unknown token")
                add = "にゃーー" .. tobinary(id):gsub("1", "にゃ"):gsub("0", "ー") .. "ん"
            end
            if #pairs ~= 0 then
                table.insert(pairs[#pairs], add)
            else
                table.insert(line, add)
            end
            ::continue::
        end
        table.insert(out, table.concat(line, ""))
    end
    return table.concat(out, "\n")
end

local function _arg_parse(arg)
    local out = {arg[1]}
    for i = 2, #arg do
        local c = arg[i]
        if c:match("^%-[^%-]") then
            for j = 2, c:len() do
                out[c:sub(j, j)] = true
            end
        else
            table.insert(out, c)
        end
    end
    return out
end

local arg = _arg_parse{...}
local file = assert(io.open(arg[1], "r"))
local prog = file:read("a")
file:close()


local log = nil
if arg[2] then
    log = assert(io.open(arg[2], "w"))
else
    if arg.r then 
        log = assert(io.open("out.meor", "w"))
    else
        log = assert(io.open("out.meow", "w"))
    end
end

assert(log)

local piled = ""
if arg.r then 
    piled = transpile_w(prog)
else
    piled = transpile_r(prog)
end

log:write(piled)
log:close()