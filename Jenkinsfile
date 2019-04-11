pipeline {
  agent {
    node {
      label 'Master'
    }

  }
  stages {
    stage('Check packages') {
      steps {
        sh 'make prepare'
      }
    }
    stage('Build') {
      steps {
        sh 'make build'
      }
    }
  }
}