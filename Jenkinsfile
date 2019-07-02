pipeline {
    
    agent any
    
    tools {
        maven 'Maven 3.5.2'
    }

    stages {
        stage ('Initialize') {
            steps {  
                script {
                    currentBuild.displayName = "#${BUILD_NUMBER} ${GIT_BRANCH}"
                }
      			sh '''
               		echo "PATH = ${PATH}"
               		echo "M2_HOME = ${M2_HOME}"
               	'''
            }
        }

        stage ('Test') {
            steps {
                sh 'mvn clean test' 
            }
        }

        stage ('Package') {
        	steps {
        		sh 'mvn clean package'
        	}
        }

        stage ('Verify') {
        	steps {
                wrap([$class: 'Xvfb', additionalOptions: '', assignedLabels: '', autoDisplayName: true, debug: true, displayNameOffset: 0, installationName: 'default', parallelBuild: true, screen: '']) {
                    sh 'mvn clean verify'
                }
        	}
        }

    }
}
