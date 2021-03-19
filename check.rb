# Written by Samuel Burns Cohen
#
# check.rb
#
# This program runs unit tests on the Leij interpreter

def parseTest(filename)
  text = File.read(filename)
  description = if match = text.match(/@description: ?(.+)/i)
                then (match.captures)[0] else "no description" end
  output = if match = text.match(/@output: ?(.+)/i)
           then (match.captures)[0] else "" end
  return [output, description]
end

def evalTest(test, expectedOutput, description)
  response = `./bin/lc -q #{test}`
  if response.strip == expectedOutput.strip then
    puts "#{description} \u001b[32mPASSED\u001b[0m"
  else
    msg = "expected #{expectedOutput.strip} but got #{response.strip}"
    puts ("#{description} \u001b[31mFAILED\u001b[0m\n" + msg)
  end
end

if ARGV.size != 1 then
  puts "Usage: ruby check.rb [path to tests directory]"
  exit 1
end

dirPath = ARGV[0];
tests = Dir.glob("#{dirPath}/**/*").select { |e|
  File.file? e and File.extname(e) == ".lj"
};

tests.each do |test|
  output, description = parseTest test
  evalTest(test, output, description)
end
